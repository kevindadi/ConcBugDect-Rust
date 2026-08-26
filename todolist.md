# Async 建模 —— 覆盖范围与待办清单

> 本文档记录 MIR → Petri 网管线中异步（`async`/`tokio`）建模的**当前覆盖范围**与**后续演进方向**，按工程优先级排列。回归测试统一后置（见 `T-001`）。

## 当前覆盖范围（已实现并验证）

| ID | 能力 | 机制 | 状态 |
| --- | ---- | ---- | ---- |
| C-001 | `tokio::spawn` 分类 | `classify_thread_control` 扩展 `AsyncSpawn`，正则命中 `tokio…::spawn` | ✅ |
| C-002 | `JoinHandle.await` 识别 | 类型判定 `classify_async_join_by_ty`（被 await future 类型含 `JoinHandle`），不依赖 def-path（blanket impl 路径不含 `JoinHandle`） | ✅ |
| C-003 | 协程 future 解析 | `resolve_closure_def_id` 支持 `TyKind::Coroutine`/`CoroutineClosure`，spawn 实参解析到协程 `(start, end)` | ✅ |
| C-004 | spawn/join 接线 | 复用 `handle_spawn`/`handle_join`：spawn 输出弧到协程 `start`，join 从任务 `end` 汇合 | ✅ |
| C-005 | 跨 await 锁 guard 识别 | `LockGuardId.field` + `register_projected_guard`，协程状态投影 `(*_state as variant#N).k` 中的 guard 按其字段索引注册并解析 receiver | ✅ |
| C-006 | 协程 upvar 数据流 | PTA env 阶段按 `tcx.is_coroutine` 分支：`_1.0 → state-heap`（状态指针），修正闭包式 `_1.field_i` 不匹配协程访问形状的问题；跨实例 `Arc<Mutex>` 别名归并到同一锁资源 | ✅ |
| C-007 | 挂起/完成语义 | `handle_return` 区分 `Poll::Pending`（挂起，续接到 continuation）与 `Poll::Ready`（完成，接函数 end） | ✅ |
| C-008 | 状态分发约束 | 协程 `bb0` 判别式 switch 仅接入口态（discriminant 0），resume 路径由挂起续接，避免"未挂起即重 poll"假路径 | ✅ |
| C-009 | Join 去重 | `.await` 降级中的 `into_future` 包装不作为 join，仅 `poll` 调用接 join，避免任务结束 token 被二次消费 | ✅ |
| C-010 | 基准验证 | `bench/deadlock/async-deadlock`：双任务 AB-BA 死锁，锁分组收敛为 2 个真实锁，`Bug count == 1` | ✅ |

覆盖效果：异步死锁（持锁跨 `.await`、任务间互等）经可达性分析可检出；spawn/join 同步边与线程模型同构。

## 待办（Roadmap）

### T-001 回归测试自动化
- **现状**：无自动化测试守护 async 建模；C-005~C-009 任一回归都无法被 CI 捕获。
- **目标**：新增 CI smoke test，对 `bench/deadlock/async-deadlock` 断言 `Bug count == 1` 且锁分组 == 2；并扩充 async bench 语料（`select!`、`tokio::sync::Mutex`、超时变体）。
- **状态**：待办（用户明确统一后置）。

### T-002 future 组合子覆盖（`select!` / `join!` / `tokio::join!`）
- **现状**：仅覆盖 `JoinHandle.await`（`poll` 调用形态）。`join!`/`select!` 宏展开为 `poll_fn` + 多 future 轮询，无单一 `poll` 调用锚点，当前分类无法命中。
- **目标**：在 `CallSiteCollector::visit_local_decl` 层识别 `futures_util::future::join::Join` / `select::Select` / `JoinAll` 组合子类型，建模"全分支汇合"（join）与"先到先得 + 取消落选分支"（select）。select 需处理落选分支的 `CoroutineDrop`（释放其持有的锁），否则误报死锁。
- **优先级**：高（`select!` 是 tokio 核心模式，目前为已知盲区）。

### T-003 挂起检测的版本鲁棒性
- **现状**：C-007 用 `_0 = Poll::Pending` 的 debug-string 启发式判定挂起，绑定当前 rustc（nightly-2026-05-29）的 MIR 形态（`SetDiscriminant` 渲染）。
- **目标**：改用结构化判定（`Rvalue::SetDiscriminant` 的 variant 与 `Poll` ADT 判别式对照，或 `Body::coroutine_kind`/`tcx.coroutine_kind`），消除对 debug 输出的依赖；对工具链升级做兼容测试。

### T-004 协程布局建模（`tcx.coroutine_layout`）
- **现状**：C-006 用状态指针 + upvar 槽位近似，未显式建模 `State.variant#N.k` 布局；对多挂起点、复杂 upvar 场景的精度依赖近似。
- **目标**：以 `tcx.coroutine_layout(def_id)` 映射 upvar 到具体 variant 字段，替代启发式投影；为 T-002/T-008 提供结构化基础。

### T-005 跨域（线程 + 任务）共享锁健全性
- **现状**：`LockGuardId.field` 使协程状态槽 guard 与普通 local guard 身份区分；`std::sync::Mutex` 在线程与任务间共享时的 receiver 别名依赖 points-to 归并，未做专项验证。
- **目标**：补充"线程持锁、异步任务阻塞"跨域用例，验证不因 sync/async 上下文判别而拆分共享锁（避免假阴性）；必要时为 receiver 别名建立专项断言。

### T-006 异步同步原语扩展
- **现状**：`LockGuardTy` 显式排除 `tokio`/`async_std`/`futures`/`loom` 的 guard；`tokio::sync::Mutex` 等异步原语未建模。
- **目标**：按需纳入 `tokio::sync::Mutex`/`RwLock`/`Semaphore`/`mpsc` 通道，映射为对应资源 place；评估其与 std 原语在挂起场景下的语义差异（取消安全性、取消时释放）。

### T-007 执行器/计时语义
- **现状**：`sleep().await` 的 Pending/Ready 分支按非确定性探索，未建模 timer 推进与超时释放。
- **目标**：为时间相关 future 引入抽象的调度 token（或显式"可恢复挂起"模型），消除"挂起即终态"的过度近似；评估对状态空间规模的影响。

### T-008 检测器扩展（async 场景）
- **现状**：死锁检测器可用；数据竞争/原子性检测对 async 场景未验证。
- **目标**：将 `.await` 挂起点作为抢占点接入原子性检测精度；验证跨任务 `UnsafeRead`/`UnsafeWrite` 的 happens-before（join 边）语义。

## 已知限制（当前不建模，作为声明）

- 执行器调度与任务优先级：任务交错由 Petri 网非确定性枚举，不区分调度策略。
- timer/超时/IO 就绪：不建模时间推进，挂起分支按非确定处理。
- `select!` 取消语义：落选分支的资源释放未建模（见 T-002）。
- 挂起检测绑定工具链版本（见 T-003）。

## 工程约束

- 所有 C-005~C-009 的翻译层改动以 `tcx.is_coroutine` / join 类型判定门控，**不影响同步代码路径**（回归已验证 `conflict-inter`/`lock-closure`/`inter`/`intra`/`static-ref`/`condvar-closure` 计数不变）。
- `LockGuardId.field` 是唯一触及共享代码的改动：sync guard 的 `field` 恒为 `None`，行为退化为原有 `(instance, local)` 语义。