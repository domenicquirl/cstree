//! Single-producer, single-consumer channel optimized for taking advantage of having only one sender and one receiver
//! to receive multiple items in bulk.

use std::{
    collections::VecDeque,
    fmt,
    sync::atomic::{AtomicBool, Ordering},
};

use parking_lot::{Condvar, Mutex};
use triomphe::Arc;

const QUEUE_INIT_CAPACITY: usize = 4096;

pub fn unbounded_spsc<T>() -> (Sender<T>, Receiver<T>) {
    let inner = Arc::new(Shared::new());
    (Sender { inner: inner.clone() }, Receiver { inner })
}

#[derive(Debug)]
struct Shared<T> {
    queue:        Mutex<VecDeque<T>>,
    notify:       Condvar,
    disconnected: AtomicBool,
}

impl<T> Shared<T> {
    fn new() -> Self {
        Self {
            queue:        Mutex::new(VecDeque::with_capacity(QUEUE_INIT_CAPACITY)),
            notify:       Condvar::new(),
            disconnected: AtomicBool::new(false),
        }
    }

    fn is_disconnected(&self) -> bool {
        self.disconnected.load(Ordering::SeqCst)
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn len(&self) -> usize {
        let queue = self.queue.lock();
        queue.len()
    }
}

#[derive(Debug)]
pub struct Sender<T: 'static> {
    inner: Arc<Shared<T>>,
}

impl<T> Sender<T> {
    pub fn send(&self, msg: T) -> Result<()> {
        let mut queue = self.inner.queue.lock();
        if self.inner.is_disconnected() {
            return Err(Disconnected);
        }
        queue.push_back(msg);
        drop(queue);
        self.inner.notify.notify_one();
        Ok(())
    }

    pub fn send_all<I>(&self, msgs: I) -> Result<()>
    where
        I: Iterator<Item = T>,
    {
        let mut queue = self.inner.queue.lock();
        if self.inner.is_disconnected() {
            return Err(Disconnected);
        }
        queue.extend(msgs);
        drop(queue);
        self.inner.notify.notify_one();
        Ok(())
    }

    pub fn is_disconnected(&self) -> bool {
        self.inner.is_disconnected()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        self.inner.disconnected.store(true, Ordering::SeqCst);
        self.inner.notify.notify_one();
    }
}

#[derive(Debug)]
pub struct Receiver<T: 'static> {
    inner: Arc<Shared<T>>,
}

impl<T> Receiver<T> {
    pub fn recv(&self) -> Result<T> {
        let mut queue = self.inner.queue.lock();
        loop {
            match queue.pop_front() {
                Some(msg) => return Ok(msg),
                None if self.inner.is_disconnected() => return Err(Disconnected),
                None => self.inner.notify.wait(&mut queue),
            }
        }
    }

    pub fn drain(&self) -> Drain<T> {
        let mut queue = self.inner.queue.lock();
        let queue = std::mem::take(&mut *queue);
        Drain { queue }
    }

    pub fn is_disconnected(&self) -> bool {
        self.inner.is_disconnected()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.inner.disconnected.store(true, Ordering::SeqCst);
    }
}

#[derive(Debug)]
pub struct Drain<T> {
    queue: VecDeque<T>,
}

impl<T> Iterator for Drain<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop_front()
    }
}

impl<T> ExactSizeIterator for Drain<T> {
    fn len(&self) -> usize {
        self.queue.len()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Disconnected;

impl fmt::Display for Disconnected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "The other end of the channel was disconnected.")
    }
}

impl std::error::Error for Disconnected {}

pub type Result<T> = std::result::Result<T, Disconnected>;
