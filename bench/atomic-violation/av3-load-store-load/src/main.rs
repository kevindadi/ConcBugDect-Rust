use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

fn main() {
    let shared = Arc::new(AtomicUsize::new(0));

    let a_shared = Arc::clone(&shared);
    let thread_a = thread::spawn(move || {
        let first = a_shared.load(Ordering::Relaxed);
        let _ = first + 1;
        let _second = a_shared.load(Ordering::Relaxed);
    });

    let b_shared = Arc::clone(&shared);
    let thread_b = thread::spawn(move || {
        b_shared.store(1, Ordering::Relaxed);
    });

    thread_a.join().unwrap();
    thread_b.join().unwrap();

    let _ = shared.load(Ordering::Relaxed);
}
