# Detection algorithms on the Petri net

How each bug mode reads the **state graph** (or explores the net) and what net pattern counts as a hit.

Shared assumption: resource identity (same lock / loc / atomic) was already fixed when building the net. Detectors only look at markings and typed transitions.

Code: `src/detect/deadlock.rs`, `datarace.rs`, `atomicity_violation.rs`, `atomic_violation_detector.rs`.

## Overview

```mermaid
flowchart TB
  MIR["MIR + alias"] --> N["Petri net N"]
  N --> SG["StateGraph SG"]

  SG --> DL["deadlock"]
  SG --> DR["datarace"]
  SG --> AT["atomic - SG path"]
  N --> AV["atomic - AV explorer"]

  DL --> P1["stuck marking / lock-stuck cycle"]
  DR --> P2["same loc: Write co-enabled with Read/Write"]
  AT --> P3["load history has ≥ 2 stores"]
  AV --> P4["AV1 / AV2 / AV3 on firing trace"]
```

Bug pattern → what we look for on the net / SG:

```mermaid
flowchart LR
  subgraph deadlock
    D1["marking with no enabled transition<br/>and not main_end"]
  end

  subgraph datarace
    R1["one marking enables<br/>UnsafeWrite L and UnsafeRead/Write L"]
  end

  subgraph atomicity
    A1["trace: Load/Store of i<br/>interrupted by Store of j on same L"]
  end
```

| Mode | Where | Bug ≅ |
| ---- | ----- | ----- |
| `deadlock` | SG | No enabled fire and not `main_end`, or stable cycle with locks stuck disabled |
| `datarace` | SG | Same loc: `UnsafeWrite` co-enabled with `UnsafeRead` / `UnsafeWrite` |
| `atomic` | SG or net trace | Interleaved Load/Store (AV*) or multi-store history before a load |
| `pointsto` | dump | no concurrency query |

Interesting `TransitionType`s: `Lock` / `Unlock` / `Wait` / `Notify`, `Spawn` / `Join`, `UnsafeRead` / `UnsafeWrite`, `AtomicLoad` / `AtomicStore` / `AtomicCmpXchg`.

---

## Deadlock (`--mode deadlock`)

**Input:** `StateGraph` → **Output:** `deadlock_report.txt`

### Pattern A — terminal non-exit marking (primary)

Report state `s` if it has **no outgoing edges** and is **not** normal exit (`main_end` has no token).

State-graph view:

```mermaid
flowchart LR
  s0(("s0")) -->|"Lock A"| s1(("s1"))
  s1 -->|"Lock B"| s2(("s2 stuck"))
  s0 -->|"finish"| ok(("main_end"))

  s2 -->|"out-degree = 0"| hit["DEADLOCK"]
  ok --> fine["OK"]
```

Net view of classic AB-BA (two threads, two mutexes):

```mermaid
flowchart TB
  Ti["thread i<br/>holds A, waits Lock B"]
  Tj["thread j<br/>holds B, waits Lock A"]

  MA[(Mutex A<br/>tokens = 0)]
  MB[(Mutex B<br/>tokens = 0)]

  Ti -.->|"holds"| MA
  Tj -.->|"holds"| MB
  Ti -->|"needs token"| MB
  Tj -->|"needs token"| MA

  Ti --> stuck["no transition enabled"]
  Tj --> stuck
  stuck --> hit["DEADLOCK"]
```

### Pattern B — cyclic wait with stuck locks (fallback)

If A finds nothing: a **stable cycle** where some (not all) locks stay disabled on every state.

```mermaid
flowchart LR
  s1(("s1")) --> s2(("s2"))
  s2 --> s3(("s3"))
  s3 --> s1

  s2 -.-> note["Lock A / Lock B disabled<br/>on every state in cycle"]
  note --> hit["DEADLOCK"]
```

### Program → net

| Program bug | Net / SG situation |
| ----------- | ------------------ |
| AB-BA lock order | Pattern A: both wait, mutex tokens unavailable |
| Condvar wait without notify | `Wait` ret needs condvar token → A |
| Channel deadlock | send/recv blocked on channel place → A |

`dependency_deadlocks` is unused (empty stub).

---

## Data race (`--mode datarace`)

**Input:** `StateGraph` → **Output:** `datarace_report.txt`

### Pattern — conflicting unsafe accesses co-enabled

In one marking `s`: same `location_id`, ≥2 sites, pair is R/W or W/W (not R/R).

```mermaid
flowchart TB
  s(("marking s"))

  s -->|"enabled"| W["UnsafeWrite(L)"]
  s -->|"enabled"| R["UnsafeRead(L)"]

  W --> L[("shared loc L")]
  R --> L

  W --> race["DATA RACE"]
  R --> race
```

Write–write:

```mermaid
flowchart LR
  s(("s")) -->|"enabled"| W1["UnsafeWrite L"]
  s -->|"enabled"| W2["UnsafeWrite L"]
  W1 --> hit["DATA RACE"]
  W2 --> hit
```

Contrast — serialized by a lock (not a race):

```mermaid
flowchart LR
  s0(("s0")) -->|"Lock M"| s1(("s1"))
  s1 -->|"UnsafeWrite L"| s2(("s2"))
  s2 -->|"Unlock M"| s3(("s3"))
  s3 -->|"UnsafeRead L"| s4(("s4"))
```

`UnsafeWrite` and `UnsafeRead` are never co-enabled in the same marking.

### Program → net

| Program bug | Net / SG situation |
| ----------- | ------------------ |
| Racy `*p` without sync | Both `Unsafe*`; same loc; some `s` enables both |
| Missing lock | No `Lock` between the two accesses |

Alias under-merge → FN. Over-merge → FP.

---

## Atomicity violation (`--mode atomic`)

| Build | Algorithm |
| ----- | --------- |
| default | SG heuristic (`AtomicityViolationDetector`) |
| `--features atomic-violation` | Net fire + AV1/2/3 (`detect_atomicity_violations`) |

### Feature path — AV patterns

Same atomic `L`, threads `i` ≠ `j`. A remote store breaks an interval of `i`:

```mermaid
sequenceDiagram
  participant i as thread i
  participant L as atomic L
  participant j as thread j

  Note over i,j: AV1 load / store / store
  i->>L: Load
  j->>L: Store
  i->>L: Store
```

```mermaid
sequenceDiagram
  participant i as thread i
  participant L as atomic L
  participant j as thread j

  Note over i,j: AV2 store / store / load
  i->>L: Store
  j->>L: Store
  i->>L: Load
```

```mermaid
sequenceDiagram
  participant i as thread i
  participant L as atomic L
  participant j as thread j

  Note over i,j: AV3 load / store / load
  i->>L: Load
  j->>L: Store
  i->>L: Load
```

```mermaid
flowchart TB
  AV1["AV1: Load_i → Store_j → Store_i"]
  AV2["AV2: Store_i → Store_j → Load_i"]
  AV3["AV3: Load_i → Store_j → Load_i"]
  AV1 --> hit["ATOMICITY VIOLATION"]
  AV2 --> hit
  AV3 --> hit
```

| Id | Shape | Meaning |
| -- | ----- | ------- |
| AV1 | Loadᵢ … Storeⱼ … Storeᵢ | Remote store before `i` stores after its load |
| AV2 | Storeᵢ … Storeⱼ … Loadᵢ | Remote store between `i`’s store and later load |
| AV3 | Loadᵢ … Storeⱼ … Loadᵢ | Remote store between two loads of `i` |

### Default path — load with ≥2 related stores in history

```mermaid
flowchart TB
  load["AtomicLoad at state s"] --> walk["walk SG predecessors"]
  walk --> stores["AtomicStore same var<br/>ordering allowed"]
  stores -->|"count ≥ 2"| hit["ATOMICITY VIOLATION"]
```

---

## What detectors do *not* decide

- Whether two guards are the same mutex (alias at construction).  
- Path feasibility / numeric branches.  
- Full memory-model HB (orders are tags / coarse filters only).
