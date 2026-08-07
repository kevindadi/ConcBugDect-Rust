# RustPTA

RustPTA is a Petri-net-based static analyzer for Rust concurrency bugs. It runs as a Rust compiler driver, collects MIR-level information during compilation, translates the analyzed program into a Petri net, builds a state graph, and reports potential concurrency problems.

The project is intended for three audiences:

- users who want to run deadlock, data-race, atomicity, or points-to analysis on Rust programs;
- researchers who want to inspect the MIR-to-Petri-net analysis pipeline;
- contributors who want to extend the translator, Petri-net model, or detectors.

## Features

- Deadlock detection (`--mode deadlock`, the default).
- Data-race detection (`--mode datarace`).
- Atomicity-violation detection (`--mode atomic`, requires the `atomic-violation` feature).
- Standalone points-to reporting (`--mode pointsto`) and optional points-to export (`--viz-pointsto`).
- DOT visualization for call graphs, MIR, Petri nets, Petri-net reduction stages, and state graphs.
- Optional Petri-net reduction before state-space construction.
- Optional partial-order reduction for state-space exploration.
- Local web viewer for browsing analysis runs and benchmark cases.

## How the analysis works

1. `pn` runs as a rustc driver and receives the same Rust compiler inputs as a normal build.
2. The compiler callback collects MIR-level function instances after rustc analysis.
3. RustPTA builds a call graph and identifies configured concurrency APIs.
4. MIR is translated into a Petri net.
5. Unless disabled, Petri-net reduction simplifies loops, sequences, and intermediate places.
6. A state graph is constructed from the final Petri net.
7. The selected detector runs on the state graph or Petri-net model.
8. Reports and visualization artifacts are written under the analysis output directory.

## Requirements

This project uses `rustc_private`, so it must be built with the nightly toolchain and rustc development components. The repository already includes `rust-toolchain.toml` with the required components:

```bash
rustup component add rust-src rustc-dev llvm-tools-preview
```

## Install

```bash
cargo install --path .
```

This installs the main binaries declared by the crate:

- `pn` — rustc-driver entry point for direct analysis; need export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH
- `cargo-pn` — Cargo wrapper used as `cargo pn`;
- `pn-web` — local web viewer for generated artifacts.

## Quick start

### Analyze a crate through Cargo

Use `cargo pn` when analyzing a normal Cargo package. The `-p/--pn-crate` value is the logical output name used by RustPTA.

```bash
cargo pn -m deadlock -p your_crate --viz-callgraph --viz-petrinet --viz-stategraph
```

### Run atomicity analysis

Atomicity detection is behind the `atomic-violation` feature.

```bash
cargo run --features atomic-violation --bin pn -- \
  -p your_crate \
  -m atomic \
  --viz-petrinet \
  --viz-stategraph \
  -- path/to/file.rs
```

### Export points-to information

```bash
cargo run --bin pn -- \
  -p your_crate \
  -m pointsto \
  --pn-analysis-dir ./tmp \
  -- path/to/file.rs
```

### Run benchmark crates

The repository also contains standalone benchmark crates under `bench/`.

For data-race benchmarks, install `pn` normally and run the target crate with `RUSTC_WRAPPER=pn` and `PN_FLAGS`:

```bash
cargo install --path . --bin pn --force
RUSTC_WRAPPER="$(command -v pn)" \
PN_FLAGS="-m datarace -p unsafe_write_read --pn-analysis-dir=tmp/unsafe_write_read" \
  cargo build --manifest-path bench/data-race/unsafe-write-read/Cargo.toml
```

For atomic-violation benchmarks, reinstall `pn` with the feature enabled before using `-m atomic`:

```bash
cargo install --path . --bin pn --features atomic-violation --force
RUSTC_WRAPPER="$(command -v pn)" \
PN_FLAGS="-m atomic -p av1_load_store_store --pn-analysis-dir=tmp/av1" \
  cargo build --manifest-path bench/atomic-violation/av1-load-store-store/Cargo.toml
```

The batch helper `./detect.sh` works well for deadlock and data-race crate directories. Atomic benchmarks still require a feature-enabled `pn` install. Inspect `datarace_report.txt` or `atomicity_report.txt` under the selected analysis directory after each run.

## Common flags


| Flag                                                        | Meaning                                                                                             |
| ----------------------------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `-m, --mode <deadlock|datarace|atomic|all|pointsto>`        | Select the analysis mode. `atomic` is accepted only when the `atomic-violation` feature is enabled. |
| `-p, --pn-crate <name>`                                     | Set the target crate/output name for Cargo-based analysis.                                          |
| `--pn-analysis-dir <path>`                                  | Set the output root for analysis artifacts.                                                         |
| `--config <file>`                                           | Load configuration from a TOML file. Defaults to `pn.toml` when present.                            |
| `--viz-callgraph`                                           | Emit `callgraph.dot`.                                                                               |
| `--viz-petrinet`                                            | Emit raw, reduced-stage, and final Petri-net DOT files.                                             |
| `--viz-stategraph`                                          | Emit `stategraph.dot`.                                                                              |
| `--viz-pointsto`                                            | Emit `points_to_report.txt`.                                                                        |
| `--viz-mir`                                                 | Emit MIR DOT files under `mir/`.                                                                    |
| `--viz-cir`                                                 | Emit `cir.yaml`.                                                                                    |
| `--stop-after <mir|callgraph|pointsto|petrinet|stategraph>` | Stop after a pipeline stage for debugging.                                                          |
| `--state-limit <N>`                                         | Cap state exploration. `0` means unlimited.                                                         |
| `--full`                                                    | Translate all functions instead of using entry-reachable filtering.                                 |
| `--crate-whitelist <a,b>`                                   | Analyze only the listed crate names.                                                                |
| `--crate-blacklist <a,b>`                                   | Exclude the listed crate names.                                                                     |
| `--no-reduce`                                               | Disable Petri-net reduction.                                                                        |
| `--por`                                                     | Enable partial-order reduction.                                                                     |
| `--no-concurrent-roots`                                     | Disable extra translation of functions that use configured concurrency APIs.                        |
| `--alias-unknown-policy <conservative|optimistic>`          | Choose how unknown alias results affect Petri-net edges.                                            |


## Output files

Artifacts are written under:

```text
<pn-analysis-dir>/<crate_or_file_stem>/
```

Typical files include:


| File                                                 | Description                                                     |
| ---------------------------------------------------- | --------------------------------------------------------------- |
| `summary.json`                                       | Run metadata, graph metrics, detector mode, and artifact names. |
| `callgraph.dot`                                      | Call graph visualization.                                       |
| `petrinet_raw.dot`                                   | Petri net before reduction.                                     |
| `petrinet.dot`                                       | Final Petri net used for state exploration.                     |
| `petrinet_reduce_1_loop.dot`                         | Petri net after loop removal.                                   |
| `petrinet_reduce_2_sequence.dot`                     | Petri net after sequence merging.                               |
| `petrinet_reduce_3_intermediate.dot`                 | Petri net after intermediate-place elimination.                 |
| `stategraph.dot`                                     | State graph built from the final Petri net.                     |
| `deadlock_report.txt` / `deadlock_report.txt.json`   | Deadlock detector report.                                       |
| `datarace_report.txt` / `datarace_report.txt.json`   | Data-race detector report.                                      |
| `atomicity_report.txt` / `atomicity_report.txt.json` | Atomicity detector report.                                      |
| `points_to_report.txt`                               | Points-to report.                                               |
| `mir/*.dot`                                          | MIR graph output when `--viz-mir` is enabled.                   |
| `cir.yaml`                                           | Concurrency IR output when `--viz-cir` is enabled.              |


## Configuration

RustPTA loads `pn.toml` by default when it exists. Use `--config <file>` to select another TOML configuration file.

Supported configuration areas include:

- `state_limit` — maximum number of states to explore, or unlimited through the CLI with `--state-limit 0`;
- `entry_reachable` — whether to translate only entry-reachable functions;
- `reduce_net` — whether to reduce the Petri net before state-graph construction;
- `por_enabled` — whether partial-order reduction is enabled;
- `translate_concurrent_roots` — whether to include functions using configured concurrency APIs and their callees;
- concurrency API regex lists for thread spawn/join, scoped spawn/join, condvars, channels, and atomics;
- `alias_unknown_policy` — `conservative` treats unknown aliases as possible aliases, while `optimistic` treats them as unlikely.

## Project structure


| Path                  | Responsibility                                                                                                                                  |
| --------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/bin/pn.rs`       | Direct `pn` binary entry point.                                                                                                                 |
| `src/bin/cargo-pn.rs` | Cargo subcommand wrapper for `cargo pn`.                                                                                                        |
| `src/bin/pn-web.rs`   | Local web viewer and artifact API.                                                                                                              |
| `src/callback.rs`     | rustc callback pipeline, artifact writing, and detector dispatch.                                                                               |
| `src/options.rs`      | CLI parsing and runtime option construction.                                                                                                    |
| `src/config.rs`       | TOML configuration model and defaults.                                                                                                          |
| `src/translate/`      | Call graph construction and MIR-to-Petri-net translation.                                                                                       |
| `src/net/`            | Petri-net data structures, DOT output, incidence logic, and reductions.                                                                         |
| `src/analysis/`       | State-space and reachability analysis.                                                                                                          |
| `src/detect/`         | Deadlock, data-race, atomicity, and async bug detectors.                                                                                        |
| `src/memory/`         | Ownership, unsafe-memory, and points-to analysis support. See [docs/pointer-analysis.md](docs/pointer-analysis.md) for the points-to data-flow. |
| `src/report/`         | Text/JSON report structures.                                                                                                                    |
| `src/util/`           | MIR DOT export, memory watcher, and helper utilities.                                                                                           |


## Known limitations

See [limitations.md](limitations.md) for the current developer-facing limitation notes. Important constraints include:

- alias precision can under-approximate resource races in ambiguous cases;
- Rust/C++11-style memory ordering is modeled heuristically;
- recursion, panic/unwind paths, and complex drop ordering are not fully modeled;
- deep analysis across FFI boundaries is not supported.

## License

See [LICENSE](LICENSE).
