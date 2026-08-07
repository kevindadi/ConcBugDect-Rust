# Rust-PN Developer Guide: Known Limitations & Constraints

This document summarizes architectural limitations and design constraints in the current Rust-PN / RustPTA codebase for contributors and downstream developers. Understanding these limits helps when extending the tool or interpreting results.

## 1. Aliasing precision vs soundness

### Limitation: resource races tend toward **under-approximation**.

- **Mechanism**: When several objects may alias the same lock or channel, the tool currently connects only the **first** matching candidate.
- **Implications**:
  - **False negatives**: Complex pointer behavior can leave alias relationships ambiguous; analysis may follow only one path and miss deadlocks or races on other paths.
  - **Join semantics**: If a join handle might refer to multiple threads, the tool does not materialize every possible join edge.

### Suggested extensions

- Change net construction so ambiguous alias candidates are connected non-deterministically (or otherwise conservatively) to improve soundness.

## 2. Memory model and atomics

### Limitation: C++11 / Rust memory order is modeled heuristically.

- **Mechanism**: Acquire/Release flavor is approximated via token flow in the Petri net.
- **Implications**:
  - **Complexity**: Manual modeling is fragile and hard to validate.
  - **Relaxed ordering**: `Relaxed` may be oversimplified and miss weak-memory behaviors.

## 3. Control flow

### Limitation: the Petri net is static and finite.

- **Recursion**: Unbounded or unpredictable recursion is not supported (the net would grow without bound, or would need richer net formalisms).
- **Panic**: Panic paths are routed loosely to function exits; unwind and drop ordering under complex control flow may be imprecise despite `drop` handling.

## 4. Foreign function interface (FFI)

- **C/C++**: Deep analysis across FFI is **not** supported. Concurrency outside analyzed Rust code is invisible to the tool.
