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

### Symptom

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

### What a real fix needs

Model the coroutine's internal state layout with `tcx.coroutine_layout(def_id)`:

1. Allocate a **state heap** for the coroutine value.
2. Bind the env param `_1`/`_1.0` so `_19` (the state pointer) points to that heap.
3. Map the `AggregateKind::Coroutine` upvars onto `State.variant#N.k` using the
   coroutine layout, so `(*_state).variant#3.0` (the Arc receiver) resolves to the
   right allocation.

This is a PTA feature (coroutine/generator state layout), independent of the
async control-flow modeling above, and carries some regression risk for other
coroutine/generator handling.

## Decision / status

- Guard recognition + spawn/join wiring: **done** and verified on the bench.
- Cross-instance `Arc<Mutex>` aliasing through coroutine state: **open gap** —
  requires the coroutine-layout PTA work above. Recorded here, not yet implemented.