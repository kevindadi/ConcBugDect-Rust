# Detection algorithms on the Petri net

How each bug mode reads the **state graph** (or explores the net) and what net pattern counts as a hit.

Pipeline before detection:

```text
Petri net N  →  StateGraph SG (reachable markings + firing edges)  →  detector
```

Shared assumption: resource identity (same lock / loc / atomic) was already fixed when building `N`. Detectors only look at markings and typed transitions.

Code: `src/detect/deadlock.rs`, `datarace.rs`, `atomicity_violation.rs`, `atomic_violation_detector.rs`.

---

## Common objects

| Object | Role |
| ------ | ---- |
| Marking | Token count per place (control BB + resource places) |
| Enabled transition | Firable under current marking (control + resource presets satisfied) |
| StateGraph node | One reachable marking (+ enabled summaries for viz/detect) |
| StateGraph edge | Fired transition: `TransitionType` + token delta |

Interesting `TransitionType`s for bugs:

- Sync: `Lock` / `RwLockRead` / `RwLockWrite` / `Unlock` / `Wait` / `Notify`
- Threads: `Spawn` / `Join`
- Memory: `UnsafeRead` / `UnsafeWrite`
- Atomics: `AtomicLoad` / `AtomicStore` / `AtomicCmpXchg`

---

## Deadlock (`--mode deadlock`)

**Input:** `StateGraph`  
**Output:** `deadlock_report.txt`

### Pattern A — terminal non-exit marking (primary)

On the state graph, a node `s` is a deadlock witness if:

1. `s` has **no outgoing edges** (no enabled firing from that marking), and  
2. `s` is **not** normal termination: no token on a place whose name contains `main_end`.

On the net this usually means: some thread tokens sit on control places waiting for `Lock` / `Wait` / `Recv`-like transitions, while the required resource tokens are held elsewhere (or never produced), so nothing can fire and `main` never reached `main_end`.

```text
marking s:  thread_i @ BB_lock,  Mutex_k.tokens = 0,  …
            no transition enabled
            main_end empty
         ⇒  report s
```

### Pattern B — cyclic wait with stuck locks (fallback)

If A finds nothing, scan **cycles** in the state graph. Keep a cycle if:

- for some lock ids, every `Lock`/`RwLock*` transition of that lock stays **disabled** on every state of the cycle, and  
- not all locks are disabled that way (filters “everything frozen”), and  
- the cycle is **stable** (all successors of cycle states stay inside the cycle).

Net reading: the system can keep stuttering in a set of markings where contended lock acquires never become enabled.

### Not used today

`dependency_deadlocks` is an empty set (lock-order graph stub). Detection is reachability / cycle based, not a separate waits-for graph.

### Typical program → net situations

| Program bug | Net / SG situation |
| ----------- | ------------------ |
| AB-BA lock order | Two `Lock` transitions each need the other’s mutex token; reachable marking with both threads before second lock, both mutexes 0/held, no fire → A |
| Self-deadlock / reentrant mistake | Same mutex place capacity 1; second `Lock` disabled forever while guard still held |
| Condvar wait without notify | `Wait` ret needs condvar token; `Notify` never fires → stuck, often A |
| Channel deadlock | send/recv blocked on channel place tokens → A |

---

## Data race (`--mode datarace`)

**Input:** `StateGraph`  
**Output:** `datarace_report.txt`

### Pattern — conflicting unsafe accesses co-enabled

For each state `s`:

1. Collect outgoing edge transitions typed `UnsafeRead` / `UnsafeWrite` (each carries `location_id` ≈ alias id, span, bb, ty).  
2. Group by `location_id`.  
3. If ≥2 **access sites** on the same location, and some pair has at least one write (R/W or W/W), report a race at `s`.

Net reading: in marking `s`, two (or more) memory events on the **same resource place identity** are simultaneously firable — no mutual exclusion in the net between them.

```text
marking s enables:
  t1 = UnsafeWrite(loc=L, …)
  t2 = UnsafeRead(loc=L, …)   or another UnsafeWrite(L)
⇒ data race on L
```

Read/read only is ignored. Site pairing prefers mixed R/W when scoring.

### Typical program → net situations

| Program bug | Net / SG situation |
| ----------- | ------------------ |
| Two threads `*p =` / `*p` without sync | Both accesses lowered to `Unsafe*`; same loc place; some marking enables both |
| Missing lock around shared raw ptr | No `Lock` serialization between the two `Unsafe*` transitions |

If alias under-merges, `location_id`s differ → this pattern never fires (FN). Over-merge → FP.

---

## Atomicity violation

Two implementations:

| Build | Algorithm | Entry |
| ----- | --------- | ----- |
| default (no feature) | State-graph heuristic | `AtomicityViolationDetector` |
| `--features atomic-violation` | Net exploration + AV1/2/3 rules | `detect_atomicity_violations` |

Mode: `--mode atomic` (feature required for the second path; callback uses net explorer when feature is on).

### Feature path — AV patterns on firing traces

Explore firings from the initial marking (bounded states/depth). Atomic transitions are events `(tid, alias, Load|Store)`.

Match three rules (same `alias`, two tids `i`≠`j`):

| Id | Bench-style name | Event shape | Meaning |
| -- | ---------------- | ----------- | ------- |
| AV1 | load–store–store | thread `i`: Load … then Store; thread `j`: Store in between | Interval after load broken by remote store before `i` stores |
| AV2 | store–store–load | thread `i`: Store … then Load; thread `j`: Store in between | Remote store between `i`’s store and later load |
| AV3 | load–store–load | thread `i`: Load … then Load; thread `j`: Store in between | Remote store between two loads of `i` |

```text
trace …  Load_i(L)  …  Store_j(L)  …  Store_i(L)  …   ⇒ AV1
```

Net role: resource place for `L` plus control/segment wiring make those interleavings reachable; the detector is **trace pattern matching**, not “stuck marking”.

### Default path — load with ≥2 related stores in history

On the state graph, for an outgoing `AtomicLoad` at state `s`, walk **incoming** history; collect `AtomicStore`s on the same `var_id` whose orderings are allowed vs the load. If ≥2 such stores, report a violation pattern (load + those stores).

Coarser than AV1/2/3; ordering filter is a small Acquire/Release-style table.

### Typical program → net situations

| Program bug | Net / SG situation |
| ----------- | ------------------ |
| Check-then-act on atomic | Load and later store of `i` with foreign store interleaved → AV* or ≥2 stores before load |
| Broken flag publish | Same alias place; stores/loads typed with order tags |

---

## Points-to (`--mode pointsto`)

Not a concurrency pattern on SG. Stops after pointer analysis / net build artifacts (`points_to_report*.txt`). No deadlock/race query.

---

## Mode vs net query (summary)

| Mode | Where | Bug ≅ |
| ---- | ----- | ----- |
| `deadlock` | SG | Unfinished terminal marking, or stable cycle with locks stuck disabled |
| `datarace` | SG | Same loc: `UnsafeWrite` co-enabled with `UnsafeRead` or `UnsafeWrite` |
| `atomic` | SG or net trace | Interleaved atomic Load/Store patterns (AV rules or multi-store history) |
| `pointsto` | analysis dump | — |

---

## What detectors do *not* decide

- Whether two guards are the same mutex (alias at construction).  
- Path feasibility / numeric branch conditions (all Switch edges may exist).  
- Full C++11/Rust memory-model HB (orders are tags / coarse filters only).
