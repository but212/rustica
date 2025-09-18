//! Function Category Implementation
//!
//! This module provides a concrete implementation of the Category and Arrow traits for Rust functions.
//! It represents the category of functions where objects are types and morphisms are functions between those types.
//!
//! # Mathematical Foundation
//!
//! The function category is one of the most fundamental categories in mathematics and computer science.
//! It satisfies all category laws and provides a natural implementation of arrow operations.
//!
//! ## Category Structure
//!
//! - **Objects**: Rust types (`A`, `B`, `C`, etc.)
//! - **Morphisms**: Functions `A → B` represented as `Arc<dyn Fn(A) -> B>`
//! - **Identity**: Identity function `id_A(x) = x`
//! - **Composition**: Function composition `(g ∘ f)(x) = g(f(x))`
//!
//! ## Laws Satisfied
//!
//! ### Category Laws
//! 1. **Identity**: `f ∘ id = f = id ∘ f`
//! 2. **Associativity**: `(h ∘ g) ∘ f = h ∘ (g ∘ f)`
//!
//! ### Arrow Laws
//! 1. **Arrow Identity**: `arrow(id) = identity_morphism`
//! 2. **Arrow Composition**: `arrow(g ∘ f) = compose_morphisms(arrow(f), arrow(g))`
//! 3. **First Laws**: Various laws governing the `first` operation
//!
//! # Usage Examples
//!
//! ## Basic Operations
//!
//! ```rust
//! use rustica::category::function_category::FunctionCategory;
//! use rustica::traits::category::Category;
//! use rustica::traits::arrow::Arrow;
//!
//! // Identity morphism
//! let id = FunctionCategory::identity_morphism::<i32>();
//! assert_eq!(id(42), 42);
//!
//! // Function lifting
//! let double = FunctionCategory::arrow(|x: i32| x * 2);
//! assert_eq!(double(21), 42);
//!
//! // Composition
//! let add_one = FunctionCategory::arrow(|x: i32| x + 1);
//! let composed = FunctionCategory::compose_morphisms(&add_one, &double);
//! assert_eq!(composed(5), 12); // double(add_one(5)) = double(6) = 12
//! ```
//!
//! ## Arrow Operations
//!
//! ```rust
//! use rustica::category::function_category::FunctionCategory;
//! use rustica::traits::arrow::Arrow;
//!
//! let double = FunctionCategory::arrow(|x: i32| x * 2);
//! let square = FunctionCategory::arrow(|x: i32| x * x);
//!
//! // Process first component of pair
//! let first_double = FunctionCategory::first(&double);
//! assert_eq!(first_double((5, "hello")), (10, "hello"));
//!
//! // Split input to multiple processors
//! let split_both = FunctionCategory::split(&double, &square);
//! assert_eq!(split_both(5), (10, 25));
//!
//! // More split examples
//! let increment = FunctionCategory::arrow(|x: i32| x + 1);
//! let negate = FunctionCategory::arrow(|x: i32| -x);
//! let split_ops = FunctionCategory::split(&increment, &negate);
//! assert_eq!(split_ops(7), (8, -7));
//!
//! // Split with different types
//! let to_string = FunctionCategory::arrow(|x: i32| x.to_string());
//! let is_even = FunctionCategory::arrow(|x: i32| x % 2 == 0);
//! let mixed_split = FunctionCategory::split(&to_string, &is_even);
//! assert_eq!(mixed_split(6), ("6".to_string(), true));
//! ```
//!
//! ## Complex Pipelines
//!
//! ```rust
//! use rustica::category::function_category::FunctionCategory;
//! use rustica::traits::category::Category;
//! use rustica::traits::arrow::Arrow;
//!
//! // Multi-stage processing pipeline
//! let pipeline = {
//!     let double = FunctionCategory::arrow(|x: i32| x * 2);
//!     let add_one = FunctionCategory::arrow(|x: i32| x + 1);
//!     let to_string = FunctionCategory::arrow(|x: i32| x.to_string());
//!     
//!     let step1 = FunctionCategory::compose_morphisms(&double, &add_one);
//!     FunctionCategory::compose_morphisms(&step1, &to_string)
//! };
//!
//! assert_eq!(pipeline(5), "11");
//! ```
//!
//! # Memory Management
//!
//! All morphisms are wrapped in `Arc` for thread-safe reference counting and efficient cloning.
//! Memory is automatically managed through Rust's ownership system.

pub use crate::traits::arrow::Arrow;
pub use crate::traits::category::Category;
use std::sync::Arc;

/// A concrete implementation of the Category and Arrow traits for functions.
///
/// This zero-sized type serves as a namespace for function category operations.
/// All methods are implemented as associated functions on the traits.
pub struct FunctionCategory;

/// Type alias for function morphisms with static lifetime bounds.
///
/// This alias encapsulates the common pattern of `Arc<dyn Fn(A) -> B + 'static>`
/// used throughout the function category implementation, making the code more
/// readable and maintainable.
pub type FunctionMorphism<A, B> = Arc<dyn Fn(A) -> B + 'static>;

impl Category for FunctionCategory {
    type Object = ();
    type Morphism<A, B> = FunctionMorphism<A, B>;

    fn identity_morphism<A>() -> Self::Morphism<A, A> {
        Arc::new(|x| x)
    }

    fn compose_morphisms<A: 'static, B: 'static, C: 'static>(
        f: &Self::Morphism<A, B>, g: &Self::Morphism<B, C>,
    ) -> Self::Morphism<A, C> {
        // Clone the Arc references to share ownership
        let f_clone = Arc::clone(f);
        let g_clone = Arc::clone(g);

        Arc::new(move |x| {
            let intermediate = f_clone(x);
            g_clone(intermediate)
        })
    }
}

impl Arrow for FunctionCategory {
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        F: Fn(B) -> C + 'static,
    {
        Arc::new(f)
    }

    fn first<B, C, D>(f: &Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: 'static,
        C: 'static,
        D: 'static,
    {
        let f_clone = Arc::clone(f);
        Arc::new(move |(b, d)| (f_clone(b), d))
    }

    fn second<B, C, D>(f: &Self::Morphism<B, C>) -> Self::Morphism<(D, B), (D, C)>
    where
        B: 'static,
        C: 'static,
        D: 'static,
    {
        let f_clone = Arc::clone(f);
        Arc::new(move |(d, b)| (d, f_clone(b)))
    }

    fn split<B, C, D>(
        f: &Self::Morphism<B, C>, g: &Self::Morphism<B, D>,
    ) -> Self::Morphism<B, (C, D)>
    where
        B: 'static + Clone,
        C: 'static,
        D: 'static,
    {
        let f_clone = Arc::clone(f);
        let g_clone = Arc::clone(g);
        Arc::new(move |b: B| (f_clone(b.clone()), g_clone(b)))
    }

    fn combine_morphisms<B, C, D, E>(
        f: &Self::Morphism<B, C>, g: &Self::Morphism<D, E>,
    ) -> Self::Morphism<(B, D), (C, E)>
    where
        B: 'static,
        C: 'static,
        D: 'static,
        E: 'static,
    {
        let f_clone = Arc::clone(f);
        let g_clone = Arc::clone(g);
        Arc::new(move |(b, d)| (f_clone(b), g_clone(d)))
    }
}

/// Convenience implementations for FunctionCategory
impl FunctionCategory {
    /// Creates a morphism from a regular function.
    ///
    /// This is a convenience method that's equivalent to `Arrow::arrow`
    /// but provides a more direct API for function lifting.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::lift(|x: i32| x * 2);
    /// assert_eq!(double(21), 42);
    /// ```
    pub fn lift<A, B, F>(f: F) -> FunctionMorphism<A, B>
    where
        F: Fn(A) -> B + 'static,
    {
        Arc::new(f)
    }

    /// Creates a morphism that applies a function to both components of a pair.
    ///
    /// This is useful when you want to apply the same transformation to both
    /// elements of a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double_both = FunctionCategory::both(|x: i32| x * 2);
    /// assert_eq!(double_both((3, 5)), (6, 10));
    /// ```
    pub fn both<A, B, F>(f: F) -> FunctionMorphism<(A, A), (B, B)>
    where
        A: 'static,
        F: Fn(A) -> B + 'static,
    {
        let f = Arc::new(f);
        Arc::new(move |(a1, a2)| (f(a1), f(a2)))
    }

    /// Creates a morphism that applies a function only if a predicate is true.
    ///
    /// If the predicate is false, the original value is returned unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double_if_even = FunctionCategory::when(
    ///     |x: &i32| x % 2 == 0,
    ///     |x: i32| x * 2
    /// );
    ///
    /// assert_eq!(double_if_even(4), 8);  // Even, so doubled
    /// assert_eq!(double_if_even(3), 3);  // Odd, so unchanged
    /// ```
    pub fn when<A, P, F>(predicate: P, transform: F) -> FunctionMorphism<A, A>
    where
        A: 'static,
        P: Fn(&A) -> bool + 'static,
        F: Fn(A) -> A + 'static,
    {
        Arc::new(move |a| if predicate(&a) { transform(a) } else { a })
    }
}

/// Macro for creating named function morphisms with type annotations.
///
/// This macro provides a convenient syntax for creating function morphisms
/// with explicit type annotations, making the code more readable and self-documenting.
///
/// # Examples
///
/// ```rust
/// use rustica::category::function_category::{FunctionCategory, function};
/// use rustica::traits::category::Category;
///
/// function!(double: i32 => i32 = |x: i32| x * 2);
/// function!(to_string: i32 => String = |x: i32| x.to_string());
///
/// assert_eq!(double(21), 42);
/// assert_eq!(to_string(42), "42");
///
/// let pipeline = FunctionCategory::compose_morphisms(&double, &to_string);
/// assert_eq!(pipeline(5), "10");
/// ```
#[macro_export]
macro_rules! function {
    ($name:ident: $input:ty => $output:ty = $body:expr) => {
        let $name: $crate::category::function_category::FunctionMorphism<$input, $output> =
            $crate::category::function_category::FunctionCategory::lift($body);
    };
}

pub use function;
