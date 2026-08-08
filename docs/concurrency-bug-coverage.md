# Concurrency bug coverage gaps

Bug class → what the net needs → what exists today.

Not a Petri encoding guide. Goal: extend **sync templates + shared events**, not full Rust semantics. Value-insensitive branches → FP is accepted; missing sync edges → FN is not.

Related: [shared-value-dataflow.md](shared-value-dataflow.md), [cfg-control-flow-completeness.md](cfg-control-flow-completeness.md).

## Status legend

| Tag | Meaning |
| --- | ------- |
| **done** | Wired + detector path for common patterns |
| **partial** | Types / some wiring exist; coverage or semantics thin |
| **gap** | Needed for the bug class; little or no support |
| **later** | Useful eventually; not blocking current roadmap |

`TransitionType` today: control (`Start`/`Goto`/`Switch`/`Return`/…), `Lock`/`Unlock`/`RwLock*`, `Wait`/`Notify`, `UnsafeRead`/`UnsafeWrite`, `AtomicLoad`/`Store`/`CmpXchg`, `Spawn`/`Join`, plus unused-ish `Inhibitor`/`Reset`.

Detectors today: `deadlock`, `datarace`, `atomic` (feature), `pointsto`.

## Gap table

| Bug class | Need in the model | Have now | Status | Next move |
| --------- | ----------------- | -------- | ------ | --------- |
| Mutex / RwLock deadlock (lock order, self-lock) | Lock resource places; acquire/release transitions; interleaving via CF + spawn/join | `Lock`/`Unlock`/`RwLock*`; RAII Drop unlock; deadlock on stuck markings | **done** | Harden wrappers / parking_lot variants; avoid FN on missed unlock |
| Condvar deadlock (missed notify, wait without lock protocol) | Condvar place; `Wait`/`Notify`; wait releases+reacquires mutex | `Wait`/`Notify` + regex/attrs | **partial** | `wait_while`, timeouts, non-std condvars; fixed arg shape is brittle |
| Channel deadlock / block | Channel place; send/recv block when empty/full | Channel places + send/recv wiring | **partial** | Real bounds (not cap=100); `select`; disconnect/close |
| Barrier / latch deadlock | Barrier place: N arrivals then release | — | **gap** | Small subnet template |
| Semaphore / pool exhaustion | Counting resource place | config mentions semaphores in concurrent-roots text only | **gap** | Counting place + acquire/release API regex |
| `Once` / init reentrancy | Once state {idle,running,done} | — | **gap** / **later** | 2–3 token abstract state, not general values |
| Raw-pointer data race | Shared loc identity; concurrent `UnsafeRead`/`Write` | Raw-ptr collect + alias merge + datarace detector | **partial** | Still raw-ptr only; no safe shared interior mutability |
| Safe shared race (`Mutex` forgotten, `Static mut`, atomics misused as data) | Broader `SharedLoc` events (not only raw ptr) | — for safe locs; atomics separate | **gap** | Introduce `SharedLoc` R/W events from alias, keep values out |
| Atomicity violation (load/store interval broken) | Atomic events + coarse thread segments / orders | `AtomicLoad`/`Store`/`CmpXchg`; feature `atomic-violation` | **partial** | RMW coverage; don’t pretend full C++11 |
| Memory-ordering / HB bugs | Release/acquire edges or vector clocks on traces | Ordering stored on transitions; not a real HB checker | **gap** | Detector-side HB on event traces; don’t color the whole net |
| Join / lifetime bugs (use after thread end, missing join) | `Spawn`/`Join` sync with thread end places | `Spawn`/`Join` wired | **partial** | Scope threads; join-handle alias precision |
| Async / tokio races & deadlocks | Task spawn, `.await` points, async Mutex | Explicitly skipped in lock typing | **later** | Separate async templates when needed; don’t mix into sync MIR net blindly |
| Panic holding a lock | Unlock on unwind/cleanup CF | Cleanup CF missing; unlock mainly Drop on happy path | **gap** (edge) | Only if we care about this class; else document as out of scope |
| Path-condition / value-dependent sync | Numeric/boolean state in marking | None by design | **later** | Optional 2–3 valued flags for protocols only; default stay value-free |

## What “all concurrency bugs” means here

In scope (skeleton + events):

- Blocking / circular wait on sync resources  
- Conflicting unsynchronized accesses to a shared location  
- Broken atomic publish/interval patterns  
- Coarse HB violations on annotated atomic events  

Out of scope (do not grow the net for these):

- General arithmetic / branch feasibility (FP ok)  
- Full stacked borrows / aliasing model  
- Full Rust memory model simulation  
- Arbitrary heap shape  

## Priority order

1. **Close FN on existing classes** — lock/condvar/channel recognition + alias identity (highest ROI).  
2. **Add missing sync templates** — barrier, semaphore, better channel close/select.  
3. **Generalize shared events** — `SharedLoc` R/W beyond raw pointers; datarace consumes that.  
4. **HB as detector pass** — use atomic order tags on traces; keep marking as P/T tokens.  
5. **Async** — only with an explicit second template set.

## Checklist for a new bug class

Before adding net machinery, answer:

1. What **resource places** (capacity/tokens) or **events** does it need?  
2. Which **API/type patterns** create them?  
3. New `TransitionType` variants, or reuse existing?  
4. Detector: stuck marking, conflicting enabled events, or trace HB?  
5. Can we keep markings value-free? If not, is a ≤3-valued abstract state enough?
