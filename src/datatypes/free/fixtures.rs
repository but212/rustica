use alloc::sync::Arc;
use core::sync::atomic::{AtomicUsize, Ordering};

use super::Free;

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

/// Command reporting its clones through the returned counter.
pub(super) fn counting_cmd(id: usize) -> (CloneCountingCmd, Arc<AtomicUsize>) {
    let counter = Arc::new(AtomicUsize::new(0));
    let cmd = CloneCountingCmd {
        id,
        clones: Arc::clone(&counter),
    };
    (cmd, counter)
}

/// Left-nested `then` chain over `depth` `Increment(1)` suspensions.
pub(super) fn then_chain(depth: usize) -> Free<TestCmd, ()> {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..depth {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    p
}

/// Right-nested `zip_with` chain of `Fetch` suspensions over `pure(0)`.
pub(super) fn right_zip_chain(depth: usize) -> Free<TestCmd, i32> {
    let mut acc: Free<TestCmd, i32> = Free::pure(0);
    for _ in 0..depth {
        acc = Free::<TestCmd, i32>::suspend(TestCmd::Fetch).zip_with(acc, |a, b| a + b);
    }
    acc
}

/// Right-nested `zip_with` chain with a `pure(1)` left operand over a `Fetch` suspension.
pub(super) fn pure_left_zip_chain(depth: usize) -> Free<TestCmd, i32> {
    let mut acc: Free<TestCmd, i32> = Free::suspend(TestCmd::Fetch);
    for _ in 0..depth {
        acc = Free::<TestCmd, i32>::pure(1).zip_with(acc, |a, b| a + b);
    }
    acc
}

/// `map` chain of `depth` increments over a `Fetch` suspension.
pub(super) fn map_chain(depth: usize) -> Free<TestCmd, i32> {
    let mut p: Free<TestCmd, i32> = Free::suspend(TestCmd::Fetch);
    for _ in 0..depth {
        p = p.map(|x| x + 1);
    }
    p
}
