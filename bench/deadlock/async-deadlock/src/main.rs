use std::sync::Arc;

use parking_lot::Mutex;

async fn task1(a: Arc<Mutex<i32>>, b: Arc<Mutex<i32>>) {
    let _ga = a.lock();
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    let _gb = b.lock();
}

async fn task2(a: Arc<Mutex<i32>>, b: Arc<Mutex<i32>>) {
    let _ga = a.lock();
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    let _gb = b.lock();
}

#[tokio::main]
async fn main() {
    let l1 = Arc::new(Mutex::new(0));
    let l2 = Arc::new(Mutex::new(0));
    let h1 = tokio::spawn(task1(l1.clone(), l2.clone()));
    let h2 = tokio::spawn(task2(l2.clone(), l1.clone()));
    let _ = h1.await;
    let _ = h2.await;
}
