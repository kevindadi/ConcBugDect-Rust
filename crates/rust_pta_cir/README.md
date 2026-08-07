# rust_pta_cir

Sync experiment crate: **Petri net → [CIR](https://github.com/kevindadi/cir)** (Concurrency Intermediate Representation).

Core `/src` stays unchanged; this crate consumes the public `Net` type and emits CIR JSON for the external `ceir` validator.

## Status (framework)


| Module      | Status                                                       |
| ----------- | ------------------------------------------------------------ |
| `ast/`      | CIR JSON data model                                          |
| `convert/`  | `PnToCirConverter` — resource + function skeleton extraction |
| `export/`   | Write `cir.json`                                             |
| `validate/` | Optional hook for `ceir` CLI (planned)                       |


## Usage (library)

```rust
use rust_petri_net_analysis::net::Net;
use rust_pta_cir::{PnToCirOptions, convert_net_to_cir, write_cir_json_pretty};

let (program, report) = convert_net_to_cir(&net, PnToCirOptions::new("my_crate"));
write_cir_json_pretty(&program, "cir.json").expect("write cir.json");
```

## CLI (stub)

```bash
cargo build -p rust_pta_cir --bin pn-cir-export
cargo run -p rust_pta_cir --bin pn-cir-export -- /tmp/cir.json my_program
```

## Validate with upstream CIR

```bash
git clone https://github.com/kevindadi/cir
cd cir && cargo build --release
./target/release/ceir /path/to/cir.json
```

## Integration plan

1. **M1 (current)**: AST + resource extraction + per-function stub statements from `TransitionType`.
2. **M2**: CFG-aware statement ordering from BB places / transition sequence.
3. **M3**: Wire into `pn-cir` driver callback (`--viz-cir` → `cir.json`) without editing core pipeline logic.

