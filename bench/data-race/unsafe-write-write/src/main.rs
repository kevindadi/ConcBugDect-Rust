use std::thread;

#[derive(Clone, Copy)]
struct SharedPtr(*mut i32);

unsafe impl Send for SharedPtr {}

impl SharedPtr {
    fn as_ptr(self) -> *mut i32 {
        self.0
    }
}

fn main() {
    let shared = Box::into_raw(Box::new(0_i32));
    let shared = SharedPtr(shared);

    let writer_a_shared = shared;
    let writer_a = thread::spawn(move || unsafe {
        let ptr = writer_a_shared.as_ptr();
        *ptr = 1;
    });

    let writer_b_shared = shared;
    let writer_b = thread::spawn(move || unsafe {
        let ptr = writer_b_shared.as_ptr();
        *ptr = 2;
    });

    writer_a.join().unwrap();
    writer_b.join().unwrap();

    unsafe {
        drop(Box::from_raw(shared.as_ptr()));
    }
}
