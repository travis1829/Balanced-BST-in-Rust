use std::sync::Arc;
use std::sync::atomic::{Ordering, AtomicUsize};
use std::iter;
use std::mem;
use crossbeam::thread;
use crossbeam::deque::{Injector, Stealer, Worker};

const NUM_THREADS: usize = 16; //number of threads in the thread pool

pub fn create_work_stealing_thread_pool<T: Send + Sync, U>(initial_task: T, 
                                                        function: unsafe fn(U, &Arc<Injector<T>>) -> (),
                                                        converter: fn(T) -> U,
                                                        curr: &AtomicUsize,
                                                        goal: usize) {
    thread::scope(|s| {
        let global = Arc::new(Injector::new());
        global.push(initial_task);
        let mut workers = Vec::new();
        let mut stealers = Arc::new(Vec::new());
        let stealers_inner = Arc::get_mut(&mut stealers).unwrap();

        for _ in 0..NUM_THREADS {
            let w = Worker::new_fifo();
            stealers_inner.push(w.stealer());
            workers.push(w);
        }
        drop(stealers_inner);

        let mut threads = Vec::new();
        for _ in (1..NUM_THREADS).rev() {
            let w = workers.pop().unwrap();
            let global = Arc::clone(&global);
            let stealers = Arc::clone(&stealers);
            threads.push(s.spawn(move |_| {
                loop {
                    let task = find_task(&w, &global, &stealers);
                    match task {
                        Some(work) => unsafe {function(converter(work), &global)},
                        None => if curr.load(Ordering::Acquire) == goal {
                            break
                        }
                    }
                }
            }));
        }
        let w = workers.pop().unwrap();
        loop {
            let task = find_task(&w, &global, &stealers);
            match task {
                Some(work) => unsafe {function(converter(work), &global)},
                None => if curr.load(Ordering::Acquire) == goal {
                    break
                }
            }
        }
    }).unwrap();
}

///directly from "https://docs.rs/crossbeam/0.8.0/crossbeam/deque/index.html"
fn find_task<T>(
    local: &Worker<T>,
    global: &Injector<T>,
    stealers: &[Stealer<T>],
) -> Option<T> {
    // Pop a task from the local queue, if not empty.
    local.pop().or_else(|| {
        // Otherwise, we need to look for a task elsewhere.
        iter::repeat_with(|| {
            // Try stealing a batch of tasks from the global queue.
            global.steal_batch_and_pop(local)
                // Or try stealing a task from one of the other threads.
                .or_else(|| stealers.iter().map(|s| s.steal()).collect())
        })
        // Loop while no task was stolen and any steal operation needs to be retried.
        .find(|s| !s.is_retry())
        // Extract the stolen task, if there is one.
        .and_then(|s| s.success())
    })
}