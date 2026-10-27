use alloc::sync::Arc;
use core::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum TestCmd {
    Increment(i32),
    Fetch,
}

#[derive(Debug)]
pub(super) struct CloneCountingCmd {
    pub(super) id: usize,
    pub(super) clones: Arc<AtomicUsize>,
}

impl Clone for CloneCountingCmd {
    fn clone(&self) -> Self {
        self.clones.fetch_add(1, Ordering::SeqCst);
        Self {
            id: self.id,
            clones: Arc::clone(&self.clones),
        }
    }
}
