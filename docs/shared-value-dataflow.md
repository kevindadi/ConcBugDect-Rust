# Shared-value discovery and data-flow wiring

Where we find shared concurrency values, how aliasing merges them into resource places, and what each detector actually consumes.

Companion: [cfg-control-flow-completeness.md](cfg-control-flow-completeness.md) (control edges), [concurrency-bug-coverage.md](concurrency-bug-coverage.md) (bug-class gaps). This note is about **resource places and the transitions that touch them**.

Code map:

| Kind | Collect | Resource places | Wire ops |
| ---- | ------- | --------------- | -------- |
| Locks | `concurrency/blocking.rs` `BlockingCollector` | `PetriNet::collect_blocking_primitives` | `calls.rs` lock/unlock, `drop_unsafe.rs` Drop |
| Condvars | same collector | same | `calls.rs` `handle_condvar_call` |
| Atomics | `concurrency/atomic.rs` `AtomicCollector` | `construct_atomic_resources` | `concurrency.rs` / `handle_atomic_call` |
| Channels | `concurrency/channel.rs` `ChannelCollector` | `construct_channel_resources` | `handle_channel_call` |
| Unsafe shared | `memory/unsafe_memory.rs` | `construct_unsafe_blocks` | `drop_unsafe.rs` reads/writes |
| Alias queries | `memory/alias_engine.rs` (+ `pointsto` / `pta`) | used when merging & matching | — |

Identity key everywhere: `AliasId { instance_id, local, optional array_index }`.

## Pipeline

```text
CallGraph instances
  → collectors (type / API scan per body)
  → alias merge → ResourceRegistry places
  → BodyToPetriNet: Call/Drop/Assign → Lock/Unlock/Wait/Notify/Atomic*/Unsafe*
  → StateGraph
  → detectors match TransitionType (+ marking)
```

Default alias engine is legacy Andersen (`AliasEngine::Legacy`). PTA is opt-in (`config.pta_engine`). Matching uses `may_alias(alias_unknown_policy)` (`conservative` | `optimistic`).

## Locks

**Detect (collect)**  
`BlockingCollector::analyze`: every local whose type is `MutexGuard` / `RwLock*Guard` (std, parking_lot/lock_api, spin; skip async/tokio/loom) or `pn_mutex_guard` / `pn_rwlock_*` attrs.

**Resolve object**  
`resolve_lock_objects`: walk moves / borrows / `Result` unwraps back to the receiver of `lock()` / `read()` / `write()`. Prefer grouping by **lock object** `AliasId`, not guard pointer.

**Resource place**  
Union-find over may-alias lock objects (fallback: guard alias). Mutex place: tokens=1, cap=1. RwLock: tokens=cap=10 (`RWLOCK_CAPACITY`). Stored in `resources.locks`.

**Wire**

| Event | Where | Net effect |
| ----- | ----- | ---------- |
| Acquire | `handle_lock_call` when dest is a guard and args are not already a guard | consume lock tokens; `TransitionType::Lock` / `RwLockRead` / `RwLockWrite` |
| Release via Drop | `handle_drop` if dropped local is a guard | produce tokens; `Unlock` |
| Release via `::drop` call | `handle_call` name contains `::drop` | same |
| Condvar wait | `handle_condvar_call` | temporarily release lock on wait enter, re-acquire on ret |

**Accuracy**

- Good for RAII std/parking_lot patterns on the main path.
- Misses: async/tokio locks, manual unlock APIs not typed as guards, field-insensitive alias merges, unlocks that only run on cleanup (no cleanup CFG).
- Acquire skipped when an arg is already a guard (pass-through helpers) — intentional.

**Consumed by** deadlock (enabled Lock transitions / stuck markings); condvar wait needs the lock place.

## Condvars

**Detect**  
Locals typed `std::sync::Condvar` or `pn_condvar`.

**Place**  
One resource place per condvar alias group (tokens=1).

**Wire** (regex / attrs from config: `condvar_notify`, `condvar_wait`)

| API | Effect |
| --- | ------ |
| notify | `Notify`: produce onto condvar place |
| wait | subnet: unlock mutex on enter; ret transition consumes condvar token + re-locks |

**Accuracy**

- Std `wait`/`notify` with recognisable signatures: ok.
- `wait_while` / timeouts / `parking_lot::Condvar` only if regex/attrs match.
- Assumes arg0 = condvar, arg1 = guard for wait — wrong shape → silent miss (`lock_node_for_guard` fails).

## Atomics

**Detect**  
Locals whose ADT path contains `::sync::atomic::` (not `Ordering`). Ops from calls: `load` / `store` / RMW names via `atomic_api_from_name`. Ordering recorded per var (first op wins for place metadata).

**Place**  
`construct_atomic_resources`: merge with `alias_atomic`; place tokens=1, cap=1. Map: `AliasId → Vec<PlaceId>`.

**Wire**  
`handle_atomic_call` → `find_atomic_matches` → load/store transitions that read/write the resource place (and per-thread ordering segment places, always enabled).

**Accuracy**

- Covers common `Atomic*` locals + load/store.
- RMW / CAS naming exists; wiring depth for RMW ops is limited.
- Ordering is heuristic (first recorded op; MIR enum encoding).
- Pointer atomics / `AtomicPtr` stores have extra helpers; not full C++11 semantics.
- Alias merge uses `alias_atomic` (can differ from lock aliasing).

**Consumed by** atomicity detectors (`AtomicLoad` / `AtomicStore` / …); not the main datarace path.

## Channels

**Detect**  
`ChannelCollector`: mpsc Sender/Receiver endpoints (type-driven).

**Place**  
Pair Sender+Receiver that share a span key → one place (tokens=0, cap=100). Endpoints map to that place.

**Wire**  
`handle_channel_call` (send/recv regex): connect call transition to channel place.

**Accuracy**

- Span-keyed pairing is brittle (same-file heuristics).
- Capacity 100 is a model constant, not the real bound.
- Cross-thread aliasing depends on PTA quality.

Deadlock may involve channel blocking; not the primary datarace signal.

## Unsafe / raw-pointer shared data

**Detect**  
`UnsafeCollector`: every local with `TyKind::RawPtr`. Operations recorded on assigns / deref / cast (bookkeeping). Resource construction uses the set of those `AliasId`s.

**Place**  
Alias-connected components → one place (tokens=1, cap=1) in `resources.unsafe_places`.

**Wire** (`process_rvalue_reads` / `process_place_writes`)

| Access | Transition |
| ------ | ---------- |
| read through may-alias unsafe place | `UnsafeRead(alias, span, bb, ty)` + read/write arcs on resource |
| write | `UnsafeWrite(...)` |

Inserts an intermediate BB place so the access sits on the control path.

**Accuracy**

- Targets raw-pointer races (matches `bench/data-race/unsafe-write-*`).
- **Not** a general shared-memory race detector: safe `&` / `&mut` / interior mutability without raw ptr are ignored.
- “Unsafe” here ≈ raw ptr local, not `unsafe { }` block dominance.
- Alias over-merge → false races; under-merge → missed races.
- No happens-before beyond Petri interleaving + whatever CF you encoded.

**Consumed by** `DataRaceDetector` — only `UnsafeRead` / `UnsafeWrite` enabled in the same state.

## What each detector needs

| Mode | Needs from data-flow | Needs from CF |
| ---- | -------------------- | ------------- |
| `deadlock` | Lock/Unlock/Wait/Notify (+ channels) on resource places | Main-path CF + spawn/join enough for current benches |
| `datarace` | UnsafeRead/Write on merged raw-ptr places | Interleavings of those transitions |
| `atomic` | AtomicLoad/Store (+ segments if feature) | Same-thread order + cross-thread interleaving |
| `pointsto` | Alias engine dump | CF optional |

## Is it accurate?

**Often accurate enough** for the patterns in `bench/`: RAII mutex deadlock, condvar wait/notify, raw-pointer data races, simple atomic load/store violations.

**Not a sound whole-program shared-memory analysis.** Main holes:

1. Recognition is type/API/regex based — unknown wrappers miss.
2. Alias precision dominates resource identity (locks, atomics, unsafe, channels).
3. Unsafe path ignores non-raw-ptr sharing.
4. Condvar wait arg convention is fixed.
5. Channel pairing by span is heuristic.
6. Unlock-on-cleanup still depends on cleanup CF (usually irrelevant for current detectors; see below).
7. Dual alias engines (legacy vs PTA) can disagree; default is legacy.

## Relation to control-flow completeness

For **current** bug classes and benches, happy-path BB-CFG is usually enough: lock acquire/release, unsafe accesses, and atomics sit on normal Call/Drop/Assign paths, not on cleanup.

Still fragile if a real bug needs unlock or a racy access only on unwind, or if `TailCall` / opaque callees hide the op. That is a coverage edge case, not the common path for today’s detectors.
