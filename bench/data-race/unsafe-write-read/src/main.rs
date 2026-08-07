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

    let writer_shared = shared;
    let writer = thread::spawn(move || unsafe {
        let ptr = writer_shared.as_ptr();
        *ptr = 1;
    });

    let reader_shared = shared;
    let reader = thread::spawn(move || unsafe {
        let ptr = reader_shared.as_ptr();
        let _ = *ptr;
    });

    writer.join().unwrap();
    reader.join().unwrap();

    unsafe {
        drop(Box::from_raw(shared.as_ptr()));
    }
}
