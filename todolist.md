# Async modeling — coverage and roadmap

> This document records the **current coverage** and the **planned evolution** of async (`async`/`tokio`) modeling in the MIR → Petri net pipeline, ordered by engineering priority. Regression testing is now in place via `scripts/smoke.sh` + CI (see `T-001`).

## Current coverage (implemented and verified)

| ID | Capability | Mechanism | Status |
| --- | ---- | ---- | ---- |
| C-001 | `tokio::spawn` classification | `classify_thread_control` extended with `AsyncSpawn`; the regex matches `tokio…::spawn` | ✅ |
| C-002 | `JoinHandle.await` recognition | Type-based check `classify_async_join_by_ty` (the awaited future's type contains `JoinHandle`); does not rely on the def-path (blanket impl paths never mention `JoinHandle`) | ✅ |
| C-003 | Coroutine future resolution | `resolve_closure_def_id` supports `TyKind::Coroutine`/`CoroutineClosure`; spawn arguments resolve to the coroutine's `(start, end)` places | ✅ |
| C-004 | spawn/join wiring | Reuses `handle_spawn`/`handle_join`: spawn adds an output arc to the coroutine `start`; join converges from the task `end` | ✅ |
| C-005 | Lock guards held across `.await` | `LockGuardId.field` + `register_projected_guard`: guards stored in coroutine state projections `(*_state as variant#N).k` are registered by field index and resolved to their receiver | ✅ |
| C-006 | Coroutine upvar dataflow | The PTA env phase branches on `tcx.is_coroutine`: `_1.0 → state-heap` (the state pointer), fixing the mismatch between closure-style `_1.field_i` and coroutine access shapes; `Arc<Mutex>` aliases across instances merge into one lock resource | ✅ |
| C-007 | Suspend/completion semantics | `handle_return` distinguishes `Poll::Pending` (suspend, routed to the continuation) from `Poll::Ready` (completion, routed to the function end) | ✅ |
| C-008 | State dispatch constraint | The coroutine `bb0` discriminant switch only wires the entry state (discriminant 0); resume paths come from suspend continuations, avoiding bogus "re-poll without suspend" paths | ✅ |
| C-009 | Join deduplication | The `into_future` wrapper in `.await` lowering is not treated as a join; only the `poll` call wires the join, so the task-completion token is not consumed twice | ✅ |
| C-010 | Benchmark validation | `bench/deadlock/async-deadlock`: two-task AB-BA deadlock; lock groups converge to the 2 real locks; `Bug count == 1` | ✅ |
| C-011 | Structured suspend detection (T-003) | `block_sets_poll_pending` is now a structured check: the `Pending` variant of the `Poll`-shaped return type is located by variant name and matched against `SetDiscriminant` / `Aggregate(Adt)` / constants (unevaluated consts by variant `DefId`, evaluated consts by discriminant bit pattern); no dependency on debug-string rendering | ✅ |
| C-012 | CI smoke regression (T-001) | `scripts/smoke.sh` + `.github/workflows/smoke.yml`: async corpus asserts bug counts and lock-group counts; sync benchmarks guard the regression baselines | ✅ |

Coverage result: async deadlocks (locks held across `.await`, mutual waits between tasks) are detected by reachability analysis; spawn/join synchronization edges are isomorphic to the thread model.

## Roadmap

### T-001 Regression test automation ✅ (done)
- **Implementation**: `scripts/smoke.sh` builds `pn`, analyzes each benchmark crate, and asserts the `Bug count` in `deadlock_report.txt` plus the `[lockgroup-detail]` lock-group count; `.github/workflows/smoke.yml` runs it on push / pull_request (`main`).
- **Completed**:
  - `bench/deadlock/async-deadlock` asserts `Bug count == 1` and lock groups `== 2`;
  - new async corpus entry `bench/deadlock/async-no-deadlock` (two tasks sharing one mutex, held across `.await`) asserts `Bug count == 0` and lock groups `== 1`, guarding against **false positives** in suspend semantics and alias merging;
  - sync regression baselines (`intra`/`inter`/`conflict-inter`/`lock-closure`/`static-ref`/`condvar-closure`) are covered by the same script, aligned with the "counts unchanged" promise in the engineering constraints.
- **Remaining (depends on T-002/T-006)**: `select!`, `tokio::sync::Mutex`, and timeout-variant corpus entries are not included yet — those paths are not modeled, so asserting on them would give a false green signal; add them together with the corresponding features.

### T-002 Future combinator coverage (`select!` / `join!` / `tokio::join!`)
- **Current state**: only `JoinHandle.await` (the `poll` call shape) is covered. `join!`/`select!` macros expand to `poll_fn` + polling of multiple futures, with no single `poll` call anchor, so the current classification cannot match them.
- **Goal**: recognize `futures_util::future::join::Join` / `select::Select` / `JoinAll` combinator types at the `CallSiteCollector::visit_local_decl` layer; model "all branches converge" (join) and "first one wins + cancel the losing branches" (select). For select, the losing branch's `CoroutineDrop` must be handled (releasing the locks it holds), otherwise deadlocks are falsely reported.
- **Priority**: high (`select!` is a core tokio pattern and currently a known blind spot).

### T-003 Version robustness of suspend detection ✅ (done)
- **Implementation**: `block_sets_poll_pending` is now a structured check. It first locates the `VariantIdx` of `Pending` from the body's return type (a `Poll`-shaped enum, identified by having both `Ready` and `Pending` variants by name), then structurally matches every `_0`-writing statement in the block: `SetDiscriminant { _0, v }`, `_0 = Aggregate(Adt(.., v, ..))`, `_0 = const` (`Const::Unevaluated` matched by variant `DefId`; evaluated consts matched by discriminant bit pattern against `adt_def.discriminants`). The last recognized `_0` write decides; the debug-string heuristic has been removed.
- **Verification**: `async-deadlock` still reports `Bug count == 1` with `2` lock groups (the suspend path is hit via the structured check); sync baseline counts are unchanged (the check is gated by `tcx.is_coroutine`, so sync paths are unaffected). The async assertions in `smoke.sh` serve as the compatibility test for toolchain upgrades.

### T-004 Coroutine layout modeling (`tcx.coroutine_layout`)
- **Current state**: C-006 approximates with the state pointer + upvar slots and does not explicitly model the `State.variant#N.k` layout; precision for multiple suspend points and complex upvar scenarios relies on the approximation.
- **Goal**: use `tcx.coroutine_layout(def_id)` to map upvars to concrete variant fields, replacing the heuristic projections; provide the structural foundation for T-002/T-008.

### T-005 Cross-domain (thread + task) shared-lock soundness
- **Current state**: `LockGuardId.field` distinguishes guards in coroutine state slots from plain local guards; receiver aliasing when a `std::sync::Mutex` is shared between threads and tasks relies on points-to merging and has not been specifically validated.
- **Goal**: add "thread holds the lock, async task blocks on it" cross-domain cases and verify that shared locks are not split by sync/async context discrimination (avoiding false negatives); add dedicated assertions for receiver aliasing if needed.

### T-006 Async synchronization primitive extension
- **Current state**: `LockGuardTy` explicitly excludes `tokio`/`async_std`/`futures`/`loom` guards; async primitives such as `tokio::sync::Mutex` are not modeled.
- **Goal**: model `tokio::sync::Mutex`/`RwLock`/`Semaphore`/`mpsc` channels on demand, mapping them to the corresponding resource places; evaluate their semantic differences from std primitives in suspend scenarios (cancellation safety, release on cancel).

### T-007 Executor/timer semantics
- **Current state**: the Pending/Ready branches of `sleep().await` are explored nondeterministically; timer advancement and timeout release are not modeled.
- **Goal**: introduce an abstract scheduling token (or an explicit "resumable suspend" model) for time-related futures, eliminating the "suspend is terminal" over-approximation; evaluate the impact on state-space size.

### T-008 Detector extensions (async scenarios)
- **Current state**: the deadlock detector works; data-race/atomicity detection has not been validated for async scenarios.
- **Goal**: feed `.await` suspend points into atomicity detection as preemption points; validate the happens-before (join edge) semantics of cross-task `UnsafeRead`/`UnsafeWrite`.

## Known limitations (currently not modeled, stated explicitly)

- Executor scheduling and task priorities: task interleavings are enumerated nondeterministically by the Petri net; scheduling policies are not distinguished.
- timer/timeout/IO readiness: time advancement is not modeled; suspend branches are treated nondeterministically.
- `select!` cancellation semantics: resource release of losing branches is not modeled (see T-002).
- Suspend detection only recognizes direct writes to `_0` within the block (`SetDiscriminant` / constant / `Aggregate(Adt)`); an indirect `Poll::Pending` write routed through a temporary is not covered (see T-003 for what is done).

## Engineering constraints

- All translation-layer changes in C-005~C-009 are gated by `tcx.is_coroutine` / join type checks and **do not affect sync code paths** (regressions verified: `conflict-inter`/`lock-closure`/`inter`/`intra`/`static-ref`/`condvar-closure` counts unchanged).
- `LockGuardId.field` is the only change touching shared code: for sync guards `field` is always `None`, degrading to the original `(instance, local)` semantics.
