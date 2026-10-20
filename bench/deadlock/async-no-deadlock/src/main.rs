// Async false-positive guard: two spawned tasks share a single mutex and hold
// it across an `.await` suspend point. There is no lock-order cycle (only one
// lock exists), so every interleaving can make progress and the analyzer must
// report zero deadlocks. Exercises suspend/resume semantics (C-007/T-003),
// cross-instance `Arc<Mutex>` alias merging (C-006), and spawn/join wiring
// (C-001..C-004) without a bug to find.
use std::sync::Arc;

use parking_lot::Mutex;

async fn task1(m: Arc<Mutex<i32>>) {
    let mut _guard = m.lock();
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    *_guard += 1;
}

async fn task2(m: Arc<Mutex<i32>>) {
    let mut _guard = m.lock();
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    *_guard += 2;
}

#[tokio::main]
async fn main() {
    let m = Arc::new(Mutex::new(0));
    let h1 = tokio::spawn(task1(m.clone()));
    let h2 = tokio::spawn(task2(m.clone()));
    let _ = h1.await;
    let _ = h2.await;
}
