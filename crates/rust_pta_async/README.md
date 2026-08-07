# rust_pta_async

Async extension crate for RustPTA. **All async-related code lives here** — core `/src` is sync-only.

## Moved from core

| Module | Purpose |
| --- | --- |
| `translate/async_context.rs` | Task lifecycle state during net construction |
| `translate/async_ppn/` | Async-PPN places, task IDs, await points |
| `translate/async_translate.rs` | `AsyncNetBuilder`, Yield site collection |
| `translate/mir_to_pn/async_control.rs` | Spawn/join wiring (`AsyncControlCtx`) |
| `translate/callgraph.rs` | Tokio/async-std API classification |
| `transition.rs` | `AsyncTransitionKind` (core uses `TransitionType::Function`) |
| `detect/async_bugs.rs` | Async bug detection hooks (stubs) |

## Binaries

| Binary | Role |
| --- | --- |
| `pn` / `cargo pn` | Sync-only core (unchanged) |
| `pn-async` / `cargo pn-async` | Async experiment driver |

```bash
cargo build -p rust_pta_async
cargo test -p rust_pta_async
cargo pn-async -m deadlock -p your_crate --viz-petrinet
```

## Module layout

```text
crates/rust_pta_async/src/
  callback/           # AsyncPTACallbacks (currently delegates to core)
  transition.rs       # AsyncTransitionKind
  translate/
    async_context.rs
    async_ppn/
    async_translate.rs
    callgraph.rs
    mir_to_pn/async_control.rs
  detect/async_bugs.rs
  memory/             # async alias analysis (future)
```
