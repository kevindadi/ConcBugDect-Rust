# Async modeling: current state and remaining gap

How `async`/`tokio` code is (and is not) modeled, what landed on the `async` branch,
and the one blocker still separating the model from a real async deadlock.

Code: `src/translate/callgraph.rs`, `src/translate/mir_to_pn/thread_control.rs`,
`src/concurrency/blocking.rs`, `src/memory/pta/builder.rs`.
Bench: `bench/deadlock/async-deadlock/`.

## What is modeled

| Piece | Mechanism | Status |
| ----- | --------- | ------ |
| `tokio::spawn` | `classify_thread_control` → `ThreadControlKind::AsyncSpawn` (regex `tokio…::spawn`); future resolved via `TyKind::Coroutine`/`CoroutineClosure` in `resolve_closure_def_id` | **done** |
| `JoinHandle.await` | type-based `classify_async_join_by_ty` on the awaited future (`JoinHandle` in the `poll`/`into_future` arg type); regex alone misses it because the callee is a `core::future` blanket impl | **done** |
| spawn/join wiring | `handle_spawn` emits an output arc to the future's `start`; `handle_join` links the spawned task's `end` into the `.await` join transition | **done** |
| guards held **across** `.await` | `BlockingCollector` + `LockGuardId.field` + `register_projected_guard`: a guard stored in the coroutine state (`(*_state as variant#N).k`) is registered with its field index and resolved receiver | **done** |

The deadlock detector runs and reports; the async deadlock bench triggers spawn/join
arcs and lock acquire/release for both tasks.

## Why `AsyncSpawn` / `AsyncJoin` classification needs the type check

`.await` on a `JoinHandle` lowers to:

```
core::future::into_future::IntoFuture::into_future   (blanket impl, def-id is in core)
core::future::future::Future::poll                   (blanket impl / Pin<&mut _>)
```

Neither def-path mentions `JoinHandle`, so a regex on `fn_path` cannot see it.
The join site is recognized by inspecting the awaited future's type
(`tokio::task::JoinHandle<…>` / `Pin<&'erased mut tokio::task::JoinHandle<…>>`),
see `classify_async_join_by_ty` in `callgraph.rs`.

## The remaining blocker: coroutine upvar layout in the PTA

> **Status (updated): fixed.** The env-binding fix below landed; the four guards
> now collapse into the two real locks with the correct AB–BA structure.

### Symptom (before the fix)

`bench/deadlock/async-deadlock` (two tasks, AB–BA lock order, guards held across
`.await`) should reduce to **one** deadlock (the two tasks deadlock on each other's
held locks). It currently reports several deadlocks because the lock grouping
splits the four guards into **four** separate `Mutex_0…Mutex_3` resources instead of
two real locks.

```
[lockgroup-detail] group0 ["{closure#0}::task1::__15(rx19fSome(1))"] = ParkingLotMutex
[lockgroup-detail] group1 ["{closure#0}::task1::__19(rx19fSome(0))"] = ParkingLotMutex
[lockgroup-detail] group2 ["{closure#0}::task2::__19(rx19fSome(0))"] = ParkingLotMutex
[lockgroup-detail] group3 ["{closure#0}::task2::__15(rx19fSome(1))"] = ParkingLotMutex
```

Expected: `task1.a` and `task2.b` are the *same* `Arc<Mutex>` (both l1), and
`task1.b` / `task2.a` are l2. Every cross-instance alias query returns `Unlikely`.

### Root cause

The `async fn` is split into a wrapper (`task1`) and a coroutine
(`task1::{closure#0}`). The wrapper constructs the coroutine:

```
_0 = {coroutine@…} { a: move _1, b: move _2 }     // AggregateKind::Coroutine
```

`builder.rs` now routes `AggregateKind::Coroutine`/`CoroutineClosure` through the
same upvar binding as closures (`clo_heap.field_i ⊇ upvar_i`, `_0 → clo_heap`), so
the construction site is captured. But the coroutine **reads** its upvars through a
different shape than a closure:

```
_19 = copy (_1.0: &mut State)          // _1 = Pin<&mut State>, _19 = state pointer
_4  = &(((*_19) as variant#3).0)       // receiver = (*state).Downcast(variant#3).0
```

Closures read `_1.field_i` directly; coroutines go `_1.0 → State → Downcast(variant) → field`.
The Phase-2 env binding (`_1.field_i ⊇ clo_heap.field_i`, `analysis.rs`) matches the
closure shape, so `_19` (the state pointer) ends up with no/incorrect points-to.
Consequently `collapsed_receiver_points_to` on the receiver `{coroutine, _19, field}`
is empty and `alias()` falls to `Unlikely`.

### The fix

In the env phase (`analysis.rs`), branch on `tcx.is_coroutine(def_id)`:

- **closures**: `_1.field_i ⊇ heap.field_i` (unchanged);
- **coroutines**: bind the state pointer `_1.field_0 → state-heap`
  (`Pin<&mut State>`, upvars read via `(*_1.0).variant#N.k`).

After the fix the lock groups are:

```
[lockgroup-detail] group0 ["{closure#0}::task1::__15(rx19fSome(1))", "{closure#0}::task2::__19(rx19fSome(0))"] = ParkingLotMutex
[lockgroup-detail] group1 ["{closure#0}::task1::__19(rx19fSome(0))", "{closure#0}::task2::__15(rx19fSome(1))"] = ParkingLotMutex
```

`group0 = task1.b + task2.a` (both l2); `group1 = task1.a + task2.b` (both l1).
The net has `Mutex_0`/`Mutex_1` and the genuine AB–BA deadlock is reachable.

## Remaining: coroutine suspend-return control flow

The aliasing fix is complete, but the bug **count** is still inflated (≈16 vs 1).
The deadlock detector flags every terminal state without `main_end`
(`detect/deadlock.rs`). The model treats a coroutine **suspend** (`_0 = Poll::Pending;
return` at the `sleep().await`) as a terminal point — a suspended task has no
outgoing edge, so "task suspended holding a lock + `main` waiting on `h1.await`"
counts as a deadlock. The one true AB–BA configuration (both tasks blocked at
`b.lock`) is among them.

A full fix needs coroutine **resume** modeling: a suspend point should let the task
be re-polled and continue to the post-await code (so a suspended task is *not*
terminal). That is a separate coroutine control-flow concern from the aliasing fix.

## Decision / status

- Guard recognition + spawn/join wiring: **done** and verified on the bench.
- Cross-instance `Arc<Mutex>` aliasing through coroutine state: **fixed** (coroutine
  env binding), verified on the bench — 4 guards collapse to 2 real locks.
- Suspend-return control flow (bug count == 1): **open gap** — needs coroutine
  resume modeling, recorded above.