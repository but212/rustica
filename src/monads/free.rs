/// Work in Progress
///
/// A free monad is a monad that allows for the construction of monadic computations
/// but it doesn't specify the underlying monad.
/// TODO: Implement typeclass implementations for the Free monad.
pub enum Free<F, A> {
    Pure(A),
    Suspend(Box<F>),
}

impl<F, A> Free<F, A> {
    pub fn pure(value: A) -> Self {
        Free::Pure(value)
    }

    pub fn suspend(effect: F) -> Self {
        Free::Suspend(Box::new(effect))
    }

    pub fn flat_map<B, Func>(self, f: Func) -> Free<F, B>
    where
        Func: FnOnce(A) -> Free<F, B>,
    {
        match self {
            Free::Pure(value) => f(value),
            Free::Suspend(effect) => Free::Suspend(effect),
        }
    }
}
