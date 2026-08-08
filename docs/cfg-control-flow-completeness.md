# MIR CFG → Petri control-flow completeness

How we embed MIR control flow into the Petri net, what is actually wired today, and where edges are missing.

Code:

- `src/translate/mir_to_pn/mod.rs` — terminator dispatch, `is_back_edge`
- `src/translate/mir_to_pn/terminator.rs` — Goto / Switch / Return / Assert
- `src/translate/mir_to_pn/calls.rs` — Call + unwind entry
- `src/translate/mir_to_pn/drop_unsafe.rs` — Drop
- `src/translate/mir_to_pn/cfg_utils.rs` — successors / back-edge helper
- `src/translate/macros.rs` — fallthrough / terminal wiring

MIR reference: [`TerminatorKind`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html).

## Verdict

We embed the **non-cleanup, basic-block CFG** of translated functions.

We do **not** embed the full MIR CFG: cleanup / unwind successors, `TailCall`, most multi-exit terminators, and unresolved callees are incomplete or dropped.

So: happy-path BB-CFG ≈ yes. Full MIR control flow ≈ no.

Main-path branches are often **over-approximate** (no discriminant constraints). Exception paths are **under-approximate** (missing edges). That matters because detectors assume control edges are there before aliasing can attach resource places correctly.

## Encoding

```text
func_start → BB0_start → … → last(BB) → term_t → start(succ)
                                      ↘ Return → func_end
```

- One start place per non-cleanup, non-empty-unreachable BB (`PlaceType::BasicBlock`, capacity 1).
- Ordinary statements inside a BB do not create control places; the token advances through the BB almost atomically.
- Intermediate places appear only when unsafe / atomic wiring pushes into `bb_graph`.
- Terminators wire `last(src) → t → start(dst)`, or into a function / global exit.

Skipped BBs (no place, cannot be a precise successor):

- `bb.is_cleanup`
- `bb.is_empty_unreachable()`

Two exits:

| Place | Used for |
| ----- | -------- |
| `func_end` | normal `Return` |
| `entry_exit.1` | panic / unwind-continue / several “terminal” kinds |

Folding cleanup into `entry_exit.1` drops unlocks and intermediate control points on unwind paths.

Loops: `is_back_edge` currently always returns `false`, so back edges are kept. `break_cfg_cycles` still defaults to `true` and still computes `back_edges`, but skipping is disabled — config and code disagree.

## Expected vs actual edges

Status: **ok** / **partial** / **missing** / **intentional**.

### Common terminators

| MIR | Expected | Actual | Status |
| --- | -------- | ------ | ------ |
| `Goto` → non-cleanup | `target` | fallthrough | ok |
| `Goto` → cleanup | cleanup CFG | `handle_panic` → `entry_exit.1` | missing |
| `SwitchInt` | all targets | one Switch transition per non-excluded target | partial — edges exist; no guard on discriminant |
| `Return` | leave function | `last → Return → func_end` | ok |
| `FalseEdge` | `real_target` only | fallthrough | ok — skip imaginary borrowck edge |
| `FalseUnwind` | `real_target` (+ cleanup) | `real_target` only | partial |
| `Call` → non-cleanup `target` | return edge (+ unwind) | wait/ret or `connect_to_target` | partial — return usually ok; unwind below |
| `Call` → cleanup `target` | cleanup CFG | panic → `entry_exit.1` | missing |
| `Drop` | `target` (+ unwind / async drop) | `Drop` → `target` (+ unlock arcs) | partial |
| `Assert` | success + optional unwind | success only | partial |

### Call / callee special cases

| Case | Expected | Actual | Status |
| ---- | -------- | ------ | ------ |
| `UnwindAction::Cleanup(u)` | edge to `u` | ignored | missing |
| `(None, Continue)` | propagate unwind | `entry_exit.1` | partial |
| `FnDef`/`Closure` in `functions_map` | enter callee, return via `func_end` | wait/ret subnet | ok |
| callee not in `functions_map` | translate or mark opaque | opaque fallthrough on caller | partial |
| `FnPtr` | callee set / top | caller `target` only | missing |
| `core::panic*` | unwind/abort | arc to `entry_exit.1` | intentional approx |
| serialize-ish fn name filter | translate or exclude explicitly | whole body skipped | missing |
| promoted MIR | usually skip | skipped in construct | intentional |

### Other terminators

| MIR | Expected | Actual | Status |
| --- | -------- | ------ | ------ |
| `TailCall` | call + return-as-self | terminal → `entry_exit.1` | missing |
| `Yield` | `resume` (+ `drop`) | `resume` only | partial |
| `InlineAsm` | all targets (+ unwind) | `targets[0]` or terminal | partial |
| `Unreachable` | no successor | terminal → `entry_exit.1` | partial |
| `UnwindResume` / `UnwindTerminate` | cleanup exit | terminal → `entry_exit.1` | partial — cleanup BBs not built |
| `CoroutineDrop` | drop path | terminal → `entry_exit.1` | missing |

### Multi-successor patterns from rustc

| Pattern | MIR successors | We wire |
| ------- | -------------- | ------- |
| `Call { Some(t), Cleanup(u) }` | `{t,u}` | usually `{t}` |
| `Assert { t, Cleanup(u) }` | `{t,u}` | `{t}` |
| `Drop { t, Cleanup(u) }` | `{t,u}` | `{t}` |
| `Drop { …, drop: Some(d) }` | `{t,u?,d}` | `{t}` |
| `Yield { resume, drop: Some(d) }` | `{resume,d}` | `{resume}` |
| `FalseUnwind { real, Cleanup(u) }` | `{real,u}` | `{real}` |
| `InlineAsm` multi-exit | many | ≤1 |

## Gaps that matter

**Must fix for trustworthy exception-aware CF**

1. Cleanup BBs have no places; `UnwindAction::Cleanup` is not wired → unlocks / sync on panic paths disappear.
2. Panic / unwind folded into `entry_exit.1` → no cleanup intermediate states.

**Wrong or incomplete on common paths**

3. `TailCall` treated as abort-style terminal.
4. Assert failure / unwind edge missing.
5. `FnPtr` and filtered / non-translated callees lose callee CFG.

**Less common**

6. `Yield.drop`, `CoroutineDrop`, async drop continuation.
7. `InlineAsm` multi-exit + unwind.
8. `break_cfg_cycles` vs `is_back_edge` mismatch (easy regression).

**Precision (edges present, meaning loose)**

9. `SwitchInt` unconstrained → larger reachable set.
10. No statement-level order inside a BB.

## Benches that hit this

| Bench | Why look here |
| ----- | ------------- |
| `bench/deadlock/panic` | cleanup / panic → global exit |
| `bench/deadlock/invalid-free` | Drop vs cleanup |
| `bench/deadlock/recursive-no-deadlock` | back-edge regression |
| `bench/deadlock/call-no-deadlock` | Call wait/ret |
| `bench/deadlock/intra`, `inter`, `wait-lock-no-deadlock` | main-path lock + Drop.unlock |
| `bench/deadlock/conflict*` | Switch over-approx / false positives |
| `bench/deadlock/lock-closure`, `static-ref`, `tikv-wrapper` | opaque / closure callees |

Quick check:

```bash
# build with RUSTC_WRAPPER=pn / cargo pn, enable --viz-mir --viz-petrinet
# then: cleanup BBs + UnwindAction::Cleanup in mir/*.dot
# must have matching BasicBlock places / control arcs in petrinet*.dot
```

## What “done” looks like

For each translated `Body`, every MIR `successors()` edge has a control path in the net:

- cleanup BBs get places;
- `UnwindAction::Cleanup` connects to them;
- `TailCall` is call+return, not a global sink;
- unresolved targets are an explicit unknown-control sink, not a silent drop.

Until then, assume only: **translated functions, non-cleanup BB-CFG**.
