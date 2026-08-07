# Deadlock benchmarks

These examples are adapted from the [lockbud](https://github.com/CodeSentryAI/lockbud) `toys/` directory. lockbud is a static analyzer for Rust concurrency and memory bugs (TSE'24).

## Cases

| Directory | Description |
| --- | --- |
| `inter` | Inter-procedural double-lock examples |
| `intra` | Intra-procedural double-lock examples |
| `conflict` | Conflicting lock order |
| `conflict-inter` | Inter-procedural conflicting lock order |
| `lock-closure` | Lock usage inside closures |
| `condvar-closure` | Condvar misuse in closures |
| `condvar-struct` | Condvar misuse in structs |
| `call-no-deadlock` | Benign case: no deadlock via calls |
| `recursive-no-deadlock` | Benign case: recursion without deadlock |
| `wait-lock-no-deadlock` | Benign case: wait without deadlock |
| `issue71` | Real-world issue case |
| `tikv-wrapper` | Real-world wrapper case |
| `static-ref` | Static reference pattern |
| `invalid-free` | Invalid free (memory-related) |
| `panic` | Panic location example |

## Run

From the project root:

```bash
./detect.sh bench/deadlock/<case>/
```

Example:

```bash
./detect.sh bench/deadlock/inter/
```
