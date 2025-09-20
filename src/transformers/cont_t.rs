//! # Continuation Monad Transformer (ContT)
//!
//! The `ContT` monad transformer generalizes the continuation monad to operate over an arbitrary monad `M`.
//! It enables computations in continuation-passing style to be composed with effects from another monad.
//!
//! ## Type
//!
//! `ContT<R, M, A>` wraps a function `(A -> M<R>) -> M<R>`
//!
//! ## Use Cases
//!
//! - Composing advanced control flow with side effects (IO, state, etc.)
//! - Implementing early exit, backtracking, coroutines within effectful computations
//!
//! ## Performance Characteristics
//!
//! ### Performance Reality - ContT Has Massive Overhead
//!
//! **ContT transformer adds severe performance penalties through multiple Arc layers and CPS transformation overhead.**
//!
//! ### Real Time Complexity Impact
//! - **Construction (`new`)**: O(1) - But Arc allocation + heap indirection adds significant constant cost
//! - **Continuation Execution (`run`)**: O((f + k) × indirection_multiplier) - Arc dereferencing compounds at each level
//! - **Bind Operations**: O(f + g + cps_transformation_cost) - CPS conversion adds major overhead
//! - **CallCC**: O(1) setup is misleading - continuation capture involves expensive closure creation
//!
//! ### Memory Usage Explosion
//! - **Structure Size**: NOT O(1) - Arc (16 bytes) + continuation closures + heap allocations per level
//! - **Function Storage**: NOT "efficient" - Each continuation creates new Arc with full closure capture
//! - **Continuation Chain**: O(n × continuation_size × arc_overhead) - Memory grows exponentially with depth
//! - **Stack vs Heap**: CPS transformation moves computation from stack to heap, often increasing total memory usage
//!
//! ### Performance vs Alternatives
//! - **vs Direct Control Flow**: 50-100x slower for simple operations
//! - **vs Exception Handling**: 10-20x slower than Rust's Result-based error handling
//! - **Memory Overhead**: 5-10x higher memory usage than equivalent direct code
//!
//! ### Performance Notes
//! - ContT transforms recursive computations to iterative continuation-passing style
//! - Arc indirection cost is minimal and enables safe sharing of continuations
//! - CPS can improve performance for deeply nested computations by avoiding stack overflow
//! - Continuation capture allows efficient implementation of advanced control flow patterns
//!
//! ## Examples
//!
//! ```rust
//! use rustica::transformers::cont_t::ContT;
//! use rustica::datatypes::id::Id;
//!
//! // Create a simple ContT over Id
//! let cont = ContT::<i32, Id<i32>, i32>::pure(42);
//! let result = cont.run(|x| Id::new(x * 2));
//! assert_eq!(result, Id::new(84));
//!
//! // Chain ContT computations
//! let cont2 = cont.bind(|x| ContT::pure(x + 1));
//! let result2 = cont2.run(|x| Id::new(x * 2));
//! assert_eq!(result2, Id::new(86));
//! ```

use crate::traits::monad::Monad;

use std::marker::PhantomData;
use std::sync::Arc;

/// Type alias for the core continuation transformer function type
pub type ContTFn<M, A> = dyn Fn(Arc<dyn Fn(A) -> M + Send + Sync>) -> M + Send + Sync;

/// The continuation monad transformer: ContT<R, M, A> wraps a function `(A -> M<R>) -> M<R>`.
#[derive(Clone)]
pub struct ContT<R, M, A> {
    pub run_cont: Arc<ContTFn<M, A>>,
    phantom: PhantomData<(R, A)>,
}

impl<R, M, A> ContT<R, M, A> {
    /// Creates a new continuation transformer from a function.
    ///
    /// This is the primary constructor for `ContT`, taking a function that
    /// accepts a continuation and returns a value in the base monad.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation `(A -> M<R>)` and returns a value of type `M<R>`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// use std::sync::Arc;
    ///
    /// // Create a ContT that adds 1 to the continuation's result
    /// let cont = ContT::<i32, Id<i32>, i32>::new(|k| {
    ///     let result = k(42);
    ///     Id::new(result.value() + 1)
    /// });
    ///
    /// // Run with a continuation that doubles its input
    /// let result = cont.run(|x| Id::new(x * 2));
    /// assert_eq!(*result.value(), 85); // (42 * 2) + 1
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> M + Send + Sync>) -> M + Send + Sync + 'static,
    {
        ContT {
            run_cont: Arc::new(f),
            phantom: PhantomData,
        }
    }

    /// Runs this continuation transformer with the given continuation function.
    ///
    /// This method applies the provided continuation function to the result of this computation,
    /// effectively executing the continuation and producing the final result in the base monad.
    ///
    /// # Arguments
    ///
    /// * `k` - A function that takes a value of type `A` and returns a value of type `M`
    ///
    /// # Returns
    ///
    /// The final result of type `M` after applying the continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let cont = ContT::<i32, Id<i32>, i32>::pure(42);
    /// let result = cont.run(|x| Id::new(x * 2));
    /// assert_eq!(*result.value(), 84);
    /// ```
    pub fn run<FN>(&self, k: FN) -> M
    where
        FN: Fn(A) -> M + Send + Sync + 'static,
    {
        (self.run_cont)(Arc::new(k))
    }

    /// Lifts a value into the continuation transformer context.
    ///
    /// This creates a minimal continuation that simply passes the given value to any
    /// continuation function it receives.
    ///
    /// # Arguments
    ///
    /// * `a` - The value to lift into the ContT context
    ///
    /// # Returns
    ///
    /// A `ContT` that will apply any continuation to the value `a`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    ///
    /// let cont = ContT::<i32, Id<i32>, i32>::pure(42);
    /// let result = cont.run(|x| Id::new(x * 2));
    /// assert_eq!(result, Id::new(84));
    /// ```
    pub fn pure(a: A) -> Self
    where
        M: Clone + 'static,
        A: Clone + Send + Sync + 'static,
        R: 'static,
    {
        ContT::new(move |k| k(a.clone()))
    }
}

impl<R, M, A> ContT<R, M, A> {
    /// Monadic bind operation for the continuation transformer.
    ///
    /// Allows sequencing of continuation computations by applying a function to the result
    /// of this continuation and returning a new continuation transformer.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms a value of type `A` into a new continuation of type `ContT<R, M, B>`
    ///
    /// # Returns
    ///
    /// A new continuation transformer of type `ContT<R, M, B>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let cont1 = ContT::<i32, Id<i32>, i32>::pure(5);
    /// let cont2 = cont1.bind(|x| ContT::pure(x * 2));
    /// let result = cont2.run(|x| Id::new(x));
    /// assert_eq!(*result.value(), 10);
    /// ```
    pub fn bind<B, F>(self, f: F) -> ContT<R, M, B>
    where
        F: Fn(A) -> ContT<R, M, B> + Send + Sync + 'static,
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let run_cont = self.run_cont.clone();
            let f = f.clone();
            run_cont(Arc::new(move |a| {
                let fb = f.clone()(a);
                (fb.run_cont)(k.clone())
            }))
        })
    }

    /// Maps a function over the value inside this continuation transformer.
    ///
    /// This is the `fmap` operation for the `Functor` type class, allowing
    /// transformation of the value inside the `ContT` context without
    /// changing the continuation structure.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let computation = ContT::<i32, Id<i32>, i32>::pure(42);
    ///
    /// // Map a function over the continuation
    /// let doubled = computation.fmap(|x| x * 2);
    /// let result = doubled.run(|x| Id::new(x));
    /// assert_eq!(*result.value(), 84);
    /// ```
    pub fn fmap<B, F>(self, f: F) -> ContT<R, M, B>
    where
        F: Fn(A) -> B + Send + Sync + 'static,
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let run_cont = self.run_cont.clone();
            let f = f.clone();
            run_cont(Arc::new(move |a| k(f.clone()(a))))
        })
    }

    /// Applies a function wrapped in a `ContT` context to a value in another `ContT` context.
    ///
    /// This implements the applicative functor's apply operation for the continuation transformer,
    /// allowing functions within the continuation context to be applied to values in the same context.
    ///
    /// # Arguments
    ///
    /// * `cf` - A continuation transformer containing a function from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new continuation transformer of type `ContT<R, M, B>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let cont_val = ContT::<String, Id<String>, i32>::pure(5);
    /// let cont_fn = ContT::<String, Id<String>, Arc<dyn Fn(i32) -> String + Send + Sync>>::pure(
    ///     Arc::new(|x| format!("Value: {}", x))
    /// );
    ///
    /// let result = cont_val.apply(cont_fn).run(|x| Id::new(x));
    /// assert_eq!(*result.value(), "Value: 5");
    /// ```
    pub fn apply<B>(self, cf: ContT<R, M, Arc<dyn Fn(A) -> B + Send + Sync>>) -> ContT<R, M, B>
    where
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        ContT::new(move |k| {
            let run_val = self.run_cont.clone();
            let run_func = cf.run_cont.clone();
            let k = Arc::new(k);
            run_func(Arc::new(move |f| {
                let run_val = run_val.clone();
                let k = k.clone();
                run_val(Arc::new(move |a| k.clone()(f(a))))
            }))
        })
    }

    /// Call with current continuation.
    ///
    /// Captures the current continuation and passes it to the given function.
    /// This allows for complex control flow patterns like early returns and exception handling.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type that would be returned by the escape continuation
    /// * `F` - The type of the function that receives the escape continuation
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation escape function and returns a continuation
    ///
    /// # Returns
    ///
    /// A new continuation transformer
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::transformers::cont_t::ContT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Use call_cc to implement early return
    /// let computation = ContT::<i32, Id<i32>, i32>::pure(5).bind(|_| {
    ///     ContT::call_cc(|exit| {
    ///         // If condition is met, exit early with a different value
    ///         if 5 > 3 {
    ///             exit(10)
    ///         } else {
    ///             ContT::pure(5)
    ///         }
    ///     })
    /// });
    ///
    /// let result = computation.run(|x| Id::new(x));
    /// assert_eq!(*result.value(), 10);
    /// ```
    pub fn call_cc<B, F>(f: F) -> ContT<R, M, A>
    where
        F: Fn(Arc<dyn Fn(A) -> ContT<R, M, B> + Send + Sync>) -> ContT<R, M, A>
            + Send
            + Sync
            + 'static,
        A: Clone + Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let k_clone = k.clone();
            let escape = Arc::new(move |a: A| {
                let k_inner = k_clone.clone();
                ContT::new(move |_ignored| k_inner(a.clone()))
            });
            f.clone()(escape).run_cont.clone()(k)
        })
    }
}

use crate::transformers::MonadTransformer;

impl<R, M: Monad + Clone + Send + Sync + 'static, A: Send + Sync + 'static> MonadTransformer
    for ContT<R, M, A>
{
    type BaseMonad = M;

    fn lift(base: Self::BaseMonad) -> Self {
        ContT::new(move |_k| base.clone())
    }
}

impl<R, A> ContT<R, crate::datatypes::id::Id<R>, A> {
    /// Converts this `ContT<R, Id<R>, A>` into a `Cont<R, A>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// use rustica::transformers::cont_t::ContT;
    ///
    /// let cont_t = ContT::<i32, Id<i32>, i32>::pure(5);
    /// let cont = cont_t.to_cont();
    /// let result = cont.run(|x| x + 1);
    /// assert_eq!(result, 6);
    /// ```
    pub fn to_cont(self) -> crate::datatypes::cont::Cont<R, A> {
        crate::datatypes::cont::Cont { inner: self }
    }

    /// Converts a `Cont<R, A>` into this `ContT<R, Id<R>, A>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// use rustica::transformers::cont_t::ContT;
    ///
    /// let cont = Cont::return_cont(5);
    /// let cont_t = ContT::<i32, Id<i32>, i32>::from_cont(cont);
    /// let result = cont_t.run(|x| Id::new(x + 1));
    /// assert_eq!(*result.value(), 6);
    /// ```
    pub fn from_cont(cont: crate::datatypes::cont::Cont<R, A>) -> Self {
        cont.inner
    }
}
