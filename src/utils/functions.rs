//! # Function Utilities
//!
//! Basic function combinators and utilities for functional programming.

/// The identity function - returns its input unchanged.
///
/// This is the identity morphism in category theory: `id: A → A`
///
/// # Category Theory
///
/// In any category, each object A has an identity morphism `id_A: A → A` such that:
/// - **Left identity**: `f ∘ id_A = f` for any morphism `f: A → B`
/// - **Right identity**: `id_B ∘ f = f` for any morphism `f: A → B`
///
/// # Use Cases
///
/// 1. **As a default function**: When you need a "do nothing" transformation
/// 2. **In higher-order functions**: `map(id)` leaves values unchanged
/// 3. **Type-level programming**: Helps the type checker in complex scenarios
/// 4. **Testing**: Verifying functor/monad laws
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use rustica::utils::functions::id;
///
/// assert_eq!(id(42), 42);
/// assert_eq!(id("hello"), "hello");
/// assert_eq!(id(vec![1, 2, 3]), vec![1, 2, 3]);
/// ```
///
/// ## With Higher-Order Functions
///
/// ```rust
/// use rustica::utils::functions::id;
///
/// let numbers = vec![1, 2, 3, 4, 5];
///
/// // Identity in map - returns the same collection
/// let same: Vec<&i32> = numbers.iter().map(id).collect();
/// assert_eq!(same, vec![&1, &2, &3, &4, &5]);
///
/// // Identity as a filter (always true)
/// let bools = vec![true, false, true];
/// let truthy: Vec<bool> = bools.into_iter().filter(|&x| id(x)).collect();
/// assert_eq!(truthy, vec![true, true]);
/// ```
///
/// ## Verifying Functor Laws
///
/// ```rust
/// use rustica::utils::functions::id;
/// use rustica::traits::functor::Functor;
///
/// // Identity law for owned values
/// let option: Option<i32> = Some(42);
/// let mapped: Option<i32> = option.fmap(|x| *x).clone();  // Explicit closure
/// assert_eq!(mapped, Some(42));
///
/// // Using id for simple value transformation
/// let value = id(42);
/// assert_eq!(value, 42);
///
/// // Note: id() has lifetime limitations with fmap()
/// // Use explicit closures for complex cases
/// let numbers = vec![1, 2, 3];
/// let same: Vec<i32> = numbers.into_iter().map(id).collect();
/// assert_eq!(same, vec![1, 2, 3]);
/// ```
///
/// ## Type Inference Helper
///
/// ```rust
/// use rustica::utils::functions::id;
///
/// // Sometimes helps the compiler infer types
/// let x = id(42_i32);  // Explicitly i32
/// ```
#[inline(always)]
pub const fn id<A>(a: A) -> A {
    a
}

/// Constant function - always returns the same value.
///
/// Creates a function that ignores its input and always returns `value`.
///
/// Note: In Rust, the returned function is monomorphic over its input type.
/// That means each constructed function has a single input type. If you want to
/// use it with different input types, construct separate functions.
///
/// # Category Theory
///
/// In category theory, this represents a constant morphism.
///
/// # Examples
///
/// ```rust
/// use rustica::utils::functions::const_fn;
///
/// // For numeric inputs
/// let always_42_num = const_fn(42);
/// assert_eq!(always_42_num(1), 42);
/// assert_eq!(always_42_num(999), 42);
///
/// // For string inputs (create a separate function instance)
/// let always_42_str = const_fn(42);
/// assert_eq!(always_42_str("anything"), 42);
/// ```
#[inline(always)]
pub fn const_fn<A: Clone, B>(value: A) -> impl Fn(B) -> A {
    move |_| value.clone()
}
