//! Function Category Implementation
//!
//! This module provides a concrete implementation of the Category and Arrow traits for functions.
//! It represents the category of functions where objects are types and morphisms are functions between those types.
//!
//! **Note**: This module replaces the deprecated `Composable` trait with category-theoretically sound
//! function composition operations.
//!
//! # Mathematical Foundation
//!
//! The function category is one of the most fundamental categories in mathematics and computer science.
//! It satisfies all category laws and provides a natural implementation of arrow operations.
//!
//! ## Category Structure
//!
//! - **Objects**: Rust types (`A`, `B`, `C`, etc.)
//! - **Morphisms**: Functions `A ??B` represented as `Arc<dyn Fn(A) -> B + 'static>`
//! - **Identity**: Identity function `id_A(x) = x`
//! - **Composition**: Function composition `(g ??f)(x) = g(f(x))`
//!
//! ## Laws Satisfied
//!
//! ### Category Laws
//! 1. **Identity**: `f ??id = f = id ??f`
//! 2. **Associativity**: `(h ??g) ??f = h ??(g ??f)`
//!
//! ### Arrow Laws
//! 1. **Arrow Identity**: `arrow(id) = identity_morphism`
//! 2. **Arrow Composition**: `arrow(g ??f) = compose_morphisms(arrow(f), arrow(g))`
//! 3. **First Laws**: Various laws governing the `first` operation
//!
//! # Usage Examples
//!
//! ## Basic Operations
//!
//! ```rust
//! use rustica::category::function_category::FunctionCategory;
//!
//! // Identity morphism
//! let id = FunctionCategory::identity_morphism::<i32>();
//! assert_eq!(id(42), 42);
//!
//! // Function lifting
//! let double = FunctionCategory::arrow(|x: i32| x * 2);
//! assert_eq!(double(21), 42);
//!
//! // Composition (category-theoretic)
//! let add_one = FunctionCategory::arrow(|x: i32| x + 1);
//! let composed = FunctionCategory::compose_morphisms(&double, &add_one);
//! assert_eq!(composed(5), 12); // double(add_one(5)) = double(6) = 12
//! ```
//!
//! ## Arrow Operations
//!
//! ```rust
//! use rustica::category::function_category::FunctionCategory;
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
//! use rustica::category::function_category::{FunctionCategory, function, compose};
//!
//! // Using the function! macro for named morphisms
//! function!(double: i32 => i32 = |x: i32| x * 2);
//! function!(add_one: i32 => i32 = |x: i32| x + 1);
//! function!(to_string: i32 => String = |x: i32| x.to_string());
//!
//! // Category-theoretic composition
//! let step1 = FunctionCategory::compose_morphisms(&add_one, &double);
//! let pipeline = FunctionCategory::compose_morphisms(&to_string, &step1);
//! assert_eq!(pipeline(5), "11");
//!
//! // Or using the compose! macro
//! let macro_pipeline = compose!(
//!     |x: i32| x.to_string(),
//!     |x: i32| x + 1,
//!     |x: i32| x * 2,
//! );
//! assert_eq!(macro_pipeline(5), "11");
//!
//! // Conditional composition
//! let conditional = FunctionCategory::then_if(
//!     &add_one,
//!     &double,
//!     |x: &i32| x % 2 == 0
//! );
//! assert_eq!(conditional(1), 4);  // (1 + 1) * 2 = 4 (2 is even)
//! assert_eq!(conditional(2), 3);  // (2 + 1) = 3 (3 is odd)
//! ```
//!
//! # Memory Management
//!
//! All morphisms are wrapped in `Arc` for cheap cloning via shared ownership.
//! Note that `Arc`'s reference counting is thread-safe, but the morphism type itself does not
//! require `Send`/`Sync` bounds.

use std::sync::Arc;

/// A concrete implementation of function category operations.
///
/// This zero-sized type serves as a namespace for function category operations.
/// All methods are implemented as inherent associated functions.
pub struct FunctionCategory;

/// Type alias for function morphisms with static lifetime bounds.
///
/// This alias encapsulates the common pattern of `Arc<dyn Fn(A) -> B + 'static>`
/// used throughout the function category implementation, making the code more
/// readable and maintainable.
pub type FunctionMorphism<A, B> = Arc<dyn Fn(A) -> B + 'static>;

/// Type alias for morphisms that operate on pairs, commonly used in arrow operations
/// like `both` where the same transformation is applied to both elements of a tuple.
pub type PairMorphism<A, B> = FunctionMorphism<(A, A), (B, B)>;

impl FunctionCategory {
    /// Creates the identity morphism for a given type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let id = FunctionCategory::identity_morphism::<i32>();
    /// assert_eq!(id(42), 42);
    /// ```
    pub fn identity_morphism<A>() -> FunctionMorphism<A, A> {
        Arc::new(|x| x)
    }

    /// Composes two morphisms category-theoretically: `(g ∘ f)(x) = g(f(x))`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let add_one = FunctionCategory::arrow(|x: i32| x + 1);
    /// let composed = FunctionCategory::compose_morphisms(&double, &add_one);
    /// assert_eq!(composed(5), 12);
    /// ```
    pub fn compose_morphisms<A: 'static, B: 'static, C: 'static>(
        g: &FunctionMorphism<B, C>, f: &FunctionMorphism<A, B>,
    ) -> FunctionMorphism<A, C> {
        let f_clone = Arc::clone(f);
        let g_clone = Arc::clone(g);

        Arc::new(move |x| {
            let intermediate = f_clone(x);
            g_clone(intermediate)
        })
    }

    /// Lifts a function to a morphism.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// assert_eq!(double(21), 42);
    /// ```
    pub fn arrow<B, C, F>(f: F) -> FunctionMorphism<B, C>
    where
        F: Fn(B) -> C + 'static,
    {
        Arc::new(f)
    }

    /// Extends a morphism to act on the first element of a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let first_double = FunctionCategory::first(&double);
    /// assert_eq!(first_double((5, "hello")), (10, "hello"));
    /// ```
    pub fn first<B: 'static, C: 'static, D: 'static>(
        f: &FunctionMorphism<B, C>,
    ) -> FunctionMorphism<(B, D), (C, D)> {
        let f_clone = Arc::clone(f);
        Arc::new(move |(b, d)| (f_clone(b), d))
    }

    /// Extends a morphism to act on the second element of a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let second_double = FunctionCategory::second(&double);
    /// assert_eq!(second_double(("hello", 5)), ("hello", 10));
    /// ```
    pub fn second<B: 'static, C: 'static, D: 'static>(
        f: &FunctionMorphism<B, C>,
    ) -> FunctionMorphism<(D, B), (D, C)> {
        let f_clone = Arc::clone(f);
        Arc::new(move |(d, b)| (d, f_clone(b)))
    }

    /// Splits input across two morphisms in parallel: `f &&& g`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let square = FunctionCategory::arrow(|x: i32| x * x);
    /// let split_both = FunctionCategory::split(&double, &square);
    /// assert_eq!(split_both(5), (10, 25));
    /// ```
    pub fn split<B, C, D>(
        f: &FunctionMorphism<B, C>, g: &FunctionMorphism<B, D>,
    ) -> FunctionMorphism<B, (C, D)>
    where
        B: 'static + Clone,
        C: 'static,
        D: 'static,
    {
        let f_clone = Arc::clone(f);
        let g_clone = Arc::clone(g);
        Arc::new(move |b: B| (f_clone(b.clone()), g_clone(b)))
    }

    /// Combines two morphisms to act on pairs: `f *** g`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let to_str = FunctionCategory::arrow(|x: i32| x.to_string());
    /// let combined = FunctionCategory::combine_morphisms(&double, &to_str);
    /// assert_eq!(combined((5, 10)), (10, "10".to_string()));
    /// ```
    pub fn combine_morphisms<B, C, D, E>(
        f: &FunctionMorphism<B, C>, g: &FunctionMorphism<D, E>,
    ) -> FunctionMorphism<(B, D), (C, E)>
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
    ///
    /// # See also
    ///
    /// * [`split`](FunctionCategory::split) - Splitting a single input to two morphisms.
    /// * [`combine_morphisms`](FunctionCategory::combine_morphisms) - Combining two different morphisms for a pair input.
    pub fn both<A, B, F>(f: F) -> PairMorphism<A, B>
    where
        A: 'static,
        F: Fn(A) -> B + 'static,
    {
        Arc::new(move |(a1, a2)| (f(a1), f(a2)))
    }

    /// Creates a morphism that applies a function only if a predicate is true.
    ///
    /// If the predicate is false, the original value is returned unchanged.
    /// This is a category-theoretic conditional morphism.
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
    ///
    /// # See also
    ///
    /// * [`then_if`](Self::then_if) - For conditional composition of two existing morphisms.
    pub fn when<A, P, F>(predicate: P, transform: F) -> FunctionMorphism<A, A>
    where
        A: 'static,
        P: Fn(&A) -> bool + 'static,
        F: Fn(A) -> A + 'static,
    {
        Arc::new(move |a| if predicate(&a) { transform(a) } else { a })
    }

    /// Creates a morphism that lifts a regular function into the category.
    ///
    /// This is an alias for the FunctionCategory::arrow method, provided for consistency
    /// with the deprecated Composable trait.
    ///
    /// # See also
    ///
    /// * [`FunctionCategory::arrow`] - The standard way to lift functions into the category.
    #[inline]
    pub fn lift<A, B, F>(f: F) -> FunctionMorphism<A, B>
    where
        F: Fn(A) -> B + 'static,
        A: 'static,
        B: 'static,
    {
        Self::arrow(f)
    }

    /// Conditionally composes two morphisms based on a predicate.
    ///
    /// Applies the first morphism, then conditionally applies the second
    /// morphism if the predicate evaluates to true on the intermediate result.
    ///
    /// # Mathematical Definition
    /// ```text
    /// then_if(f, g, p) = λx. let y = f(x) in if p(y) then g(y) else y
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let add_one = FunctionCategory::arrow(|x: i32| x + 1);
    /// let double = FunctionCategory::arrow(|x: i32| x * 2);
    /// let is_even = |x: &i32| x % 2 == 0;
    ///
    /// let conditional = FunctionCategory::then_if(&add_one, &double, is_even);
    /// assert_eq!(conditional(1), 4);  // (1 + 1) * 2 = 4 (2 is even)
    /// assert_eq!(conditional(2), 3);  // (2 + 1) = 3 (3 is odd)
    /// ```
    ///
    /// # See also
    ///
    /// * [`when`](Self::when) - For lifting a single function with a predicate.
    pub fn then_if<A, P>(
        first: &FunctionMorphism<A, A>, second: &FunctionMorphism<A, A>, predicate: P,
    ) -> FunctionMorphism<A, A>
    where
        A: 'static,
        P: Fn(&A) -> bool + 'static,
    {
        let first_clone = Arc::clone(first);
        let second_clone = Arc::clone(second);

        Arc::new(move |x| {
            let result = first_clone(x);
            if predicate(&result) {
                second_clone(result)
            } else {
                result
            }
        })
    }

    /// Creates a morphism that applies multiple transformations in sequence.
    ///
    /// when the functions don't need to be reused.
    ///
    /// If the vector is empty, the resulting morphism is the identity function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::category::function_category::FunctionCategory;
    ///
    /// let pipeline = FunctionCategory::sequence(vec![
    ///     |x: i32| x + 1,
    ///     |x: i32| x * 2,
    ///     |x: i32| x - 3,
    /// ]);
    /// assert_eq!(pipeline(5), 9); // ((5 + 1) * 2) - 3 = 9
    /// ```
    pub fn sequence<A, F>(functions: Vec<F>) -> FunctionMorphism<A, A>
    where
        A: 'static,
        F: Fn(A) -> A + 'static,
    {
        Arc::new(move |initial| functions.iter().fold(initial, |acc, f| f(acc)))
    }
}

/// Macro for creating named function morphisms with type annotations.
///
/// This macro provides a convenient syntax for creating function morphisms
/// with explicit type annotations, making the code more readable and self-documenting.
/// This replaces the deprecated Composable trait functionality.
///
/// # Examples
///
/// ```rust
/// use rustica::category::function_category::{function, FunctionCategory};
///
/// function!(double: i32 => i32 = |x: i32| x * 2);
/// function!(to_string: i32 => String = |x: i32| x.to_string());
///
/// assert_eq!(double(21), 42);
/// assert_eq!(to_string(42), "42");
///
/// // Example of composing the created morphisms
/// let pipeline = FunctionCategory::compose_morphisms(&to_string, &double);
/// assert_eq!(pipeline(5), "10");
/// ```
#[macro_export]
macro_rules! function {
    ($name:ident: $input:ty => $output:ty = $body:expr) => {
        let $name = { $crate::category::function_category::FunctionCategory::arrow($body) };
    };
}

/// Macro for composing multiple functions with type annotations.
///
/// This macro provides a convenient way to compose multiple functions.
///
/// # Examples
///
/// ```rust
/// use rustica::category::function_category::compose;
///
/// let pipeline = compose!(
///     |x: i32| x.to_string(),
///     |x: i32| x * 2,
///     |x: i32| x + 1
/// );
/// assert_eq!(pipeline(5), "12");
/// ```
#[macro_export]
macro_rules! compose {
    ($first:expr) => {
        $crate::category::function_category::FunctionCategory::arrow($first)
    };
    ($first:expr, $($rest:expr),+ $(,)?) => {
        {
            let first_morphism = $crate::category::function_category::FunctionCategory::arrow($first);
            let rest_morphism = compose!($($rest),+);
            $crate::category::function_category::FunctionCategory::compose_morphisms(&first_morphism, &rest_morphism)
        }
    };
}

/// Macro for creating function pipelines using comma-separated syntax.
///
/// This macro provides a left-to-right composition syntax where functions
/// are applied in the order they appear, separated by commas.
/// Returns a composed function rather than executing immediately.
///
/// # Examples
///
/// ```rust
/// use rustica::category::function_category::pipe;
///
/// let pipeline = pipe!(|x: i32| x + 1, |x: i32| x * 2, |x: i32| x.to_string());
/// assert_eq!(pipeline(5), "12");
/// ```
#[macro_export]
macro_rules! pipe {
    ($func:expr) => {
        $crate::category::function_category::FunctionCategory::arrow($func)
    };
    ($first:expr, $($rest:expr),+ $(,)?) => {
        {
            let first_morphism = $crate::category::function_category::FunctionCategory::arrow($first);
            let rest_morphism = pipe!($($rest),+);
            $crate::category::function_category::FunctionCategory::compose_morphisms(&rest_morphism, &first_morphism)
        }
    };
}

pub use {compose, function, pipe};

#[cfg(test)]
mod unit_tests {
    use super::FunctionCategory;

    #[test]
    fn inherent_api_composes_functions_and_pairs() {
        let id = FunctionCategory::identity_morphism::<i32>();
        assert_eq!(id(42), 42);

        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let add_one = FunctionCategory::arrow(|x: i32| x + 1);
        assert_eq!(
            FunctionCategory::compose_morphisms(&add_one, &double)(5),
            11
        );
        assert_eq!(
            FunctionCategory::compose_morphisms(&double, &add_one)(5),
            12
        );
        assert_eq!(
            FunctionCategory::first(&double)((10, "keep".to_string())),
            (20, "keep".to_string())
        );
        assert_eq!(
            FunctionCategory::second(&double)(("keep".to_string(), 10)),
            ("keep".to_string(), 20)
        );
        assert_eq!(
            FunctionCategory::split(&double, &FunctionCategory::arrow(|x: i32| x * x))(4),
            (8, 16)
        );
        let to_str = FunctionCategory::arrow(|x: i32| x.to_string());
        assert_eq!(
            FunctionCategory::combine_morphisms(&double, &to_str)((5, 10)),
            (10, "10".to_string())
        );
    }
}
