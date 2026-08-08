# ConcBugDect-Rust

ConcBugDect-Rust is a Petri-net-based static analyzer for Rust concurrency bugs. It runs as a Rust compiler driver, collects MIR-level information during compilation, translates the analyzed program into a Petri net, builds a state graph, and reports potential concurrency problems.

The crate name is `conc_bug_detector`. The installed binaries remain `pn` and `cargo-pn` (`cargo pn`).

## Features

- Deadlock detection (`--mode deadlock`, the default).
- Data-race detection (`--mode datarace`).
- Atomicity-violation detection (`--mode atomic`).
- Standalone points-to reporting (`--mode pointsto`) and optional points-to export (`--viz-pointsto`).
- DOT visualization for call graphs, MIR, Petri nets, Petri-net reduction stages, and state graphs.
- Optional Petri-net reduction before state-space construction.
- Optional partial-order reduction for state-space exploration.

## How the analysis works

1. `pn` runs as a rustc driver and receives the same Rust compiler inputs as a normal build.
2. The compiler callback collects MIR-level function instances after rustc analysis.
3. The analyzer builds a call graph and identifies configured concurrency APIs.
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

This installs:

- `pn` — rustc-driver entry point for direct analysis  
  On Linux/macOS you typically also need:
  `export LD_LIBRARY_PATH="$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH"`
- `cargo-pn` — Cargo wrapper used as `cargo pn`

## Quick start

### Analyze a crate through Cargo

Use `cargo pn` when analyzing a normal Cargo package. The `-p/--pn-crate` value is the logical output name used for artifacts.

```bash
cargo pn -m deadlock -p your_crate --viz-callgraph --viz-petrinet --viz-stategraph
```

### Run atomicity analysis

All detectors share the same Petri net and state graph; `--mode atomic` runs the
AV1/AV2/AV3 witness search over that state graph.

```bash
cargo run --bin pn -- \
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

Standalone benchmarks live under [`bench/`](bench/) (from [RustPTA/bench](https://github.com/kevindadi/RustPTA/tree/master/bench)):

- `bench/deadlock/`
- `bench/data-race/`
- `bench/atomic-violation/`

For data-race benchmarks, install `pn` and analyze with `RUSTC_WRAPPER=pn` and `PN_FLAGS`:

```bash
cargo install --path . --bin pn --force
RUSTC_WRAPPER="$(command -v pn)" \
PN_FLAGS="-m datarace -p unsafe_write_read --pn-analysis-dir=tmp/unsafe_write_read" \
  cargo build --manifest-path bench/data-race/unsafe-write-read/Cargo.toml
```

For atomic-violation benchmarks:

```bash
RUSTC_WRAPPER="$(command -v pn)" \
PN_FLAGS="-m atomic -p av1_load_store_store --pn-analysis-dir=tmp/av1" \
  cargo build --manifest-path bench/atomic-violation/av1-load-store-store/Cargo.toml
```

### Batch-analyze crates under a directory

`./detect.sh` builds `pn` and runs analysis on every crate under a directory. Options after the directory are forwarded to `pn` via `PN_FLAGS` (`-p` is set per crate).

```bash
./detect.sh bench/deadlock/ -m deadlock --viz-petrinet --pn-analysis-dir=tmp/out
```

Default flags when none are given:

```text
-m deadlock --pn-analysis-dir=<repo>/tmp
```

## Common flags

| Flag                                                        | Meaning                                                                                             |
| ----------------------------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `-m, --mode <deadlock\|datarace\|atomic\|all\|pointsto>`    | Select the analysis mode. |
| `-p, --pn-crate <name>`                                     | Set the target crate/output name for Cargo-based analysis.                                          |
| `--pn-analysis-dir <path>`                                  | Set the output root for analysis artifacts.                                                         |
| `--config <file>`                                           | Load configuration from a TOML file. Defaults to `pn.toml` when present.                            |
| `--viz-callgraph`                                           | Emit `callgraph.dot`.                                                                               |
| `--viz-petrinet`                                            | Emit raw, reduced-stage, and final Petri-net DOT files.                                             |
| `--viz-stategraph`                                          | Emit `stategraph.dot`.                                                                              |
| `--viz-pointsto`                                            | Emit `points_to_report.txt`.                                                                        |
| `--viz-mir`                                                 | Emit MIR DOT files under `mir/`.                                                                    |
| `--viz-cir`                                                 | Emit `cir.yaml`.                                                                                    |
| `--stop-after <mir\|callgraph\|pointsto\|petrinet\|stategraph>` | Stop after a pipeline stage for debugging.                                                      |
| `--state-limit <N>`                                         | Cap state exploration. `0` means unlimited.                                                         |
| `--full`                                                    | Translate all functions instead of using entry-reachable filtering.                                 |
| `--crate-whitelist <a,b>`                                   | Analyze only the listed crate names.                                                                |
| `--crate-blacklist <a,b>`                                   | Exclude the listed crate names.                                                                     |
| `--no-reduce`                                               | Disable Petri-net reduction.                                                                        |
| `--por`                                                     | Enable partial-order reduction.                                                                     |
| `--no-concurrent-roots`                                     | Disable extra translation of functions that use configured concurrency APIs.                        |
| `--alias-unknown-policy <conservative\|optimistic>`          | Choose how unknown alias results affect Petri-net edges.                                            |

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

The analyzer loads `pn.toml` by default when it exists. Use `--config <file>` to select another TOML configuration file.

Supported configuration areas include:

- `state_limit` — maximum number of states to explore, or unlimited through the CLI with `--state-limit 0`;
- `entry_reachable` — whether to translate only entry-reachable functions;
- `reduce_net` — whether to reduce the Petri net before state-graph construction;
- `por_enabled` — whether partial-order reduction is enabled;
- `translate_concurrent_roots` — whether to include functions using configured concurrency APIs and their callees;
- concurrency API regex lists for thread spawn/join, scoped spawn/join, condvars, channels, and atomics;
- `alias_unknown_policy` — `conservative` treats unknown aliases as possible aliases, while `optimistic` treats them as unlikely.

## Project structure

This repository is a single Cargo package (not a workspace).

| Path                  | Responsibility                                                    |
| --------------------- | ----------------------------------------------------------------- |
| `src/bin/pn.rs`       | Direct `pn` binary entry point.                                   |
| `src/bin/cargo-pn.rs` | Cargo subcommand wrapper for `cargo pn`.                          |
| `src/callback.rs`     | rustc callback pipeline, artifact writing, and detector dispatch. |
| `src/options.rs`      | CLI parsing and runtime option construction.                      |
| `src/config.rs`       | TOML configuration model and defaults.                            |
| `src/translate/`      | Call graph construction and MIR-to-Petri-net translation.         |
| `src/net/`            | Petri-net data structures, DOT output, incidence logic, and reductions. |
| `src/analysis/`       | State-space and reachability analysis.                            |
| `src/detect/`         | Deadlock, data-race, and atomicity detectors.                     |
| `src/memory/`         | Ownership, unsafe-memory, and points-to analysis support.         |
| `src/report/`         | Text/JSON report structures.                                      |
| `src/util/`           | MIR DOT export, memory watcher, and helper utilities.             |
| `detect.sh`           | Batch helper for analyzing crates under a directory.              |
| `bench/`              | Deadlock, data-race, and atomicity-violation benchmark crates.    |
| `docs/`               | Design notes (e.g. CFG→Petri control-flow completeness).          |

## Known limitations

- Alias precision can under-approximate resource races in ambiguous cases.
- Rust/C++11-style memory ordering is modeled heuristically.
- Recursion, panic/unwind paths, and complex drop ordering are not fully modeled.
- Deep analysis across FFI boundaries is not supported.

MIR CFG embedding covers the non-cleanup BB happy path only; cleanup/unwind, `TailCall`, etc. are incomplete. Details: [docs/cfg-control-flow-completeness.md](docs/cfg-control-flow-completeness.md). How locks / atomics / condvars / unsafe raw pointers are found and wired: [docs/shared-value-dataflow.md](docs/shared-value-dataflow.md). Bug class → model needs → coverage gaps: [docs/concurrency-bug-coverage.md](docs/concurrency-bug-coverage.md). How detectors read the net / state graph: [docs/detection-algorithms.md](docs/detection-algorithms.md).

## License

See [LICENSE](LICENSE).
