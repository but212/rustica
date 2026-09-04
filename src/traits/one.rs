//! Multiplicative identity element for types supporting multiplication.
//!
//! Defines the multiplicative identity for algebraic structures such as
//! [`Product`](crate::datatypes::wrapper::product::Product).

/// Multiplicative identity element.
///
/// Implementors must guarantee the identity laws for all `x: Self`:
///
/// - `x * Self::one() == x`
/// - `Self::one() * x == x`
///
/// # Examples
///
/// ```
/// use rustica::traits::one::One;
///
/// assert_eq!(i32::one(), 1);
/// assert_eq!(5 * i32::one(), 5);
/// ```
pub trait One: Sized {
    /// Returns the multiplicative identity element of `Self`.
    fn one() -> Self;
}

macro_rules! impl_one {
    ($($t:ty = $val:expr),* $(,)?) => {
        $(
            impl One for $t {
                #[inline]
                fn one() -> Self {
                    $val
                }
            }
        )*
    };
}

impl_one!(
    u8 = 1,
    u16 = 1,
    u32 = 1,
    u64 = 1,
    u128 = 1,
    usize = 1,
    i8 = 1,
    i16 = 1,
    i32 = 1,
    i64 = 1,
    i128 = 1,
    isize = 1,
    f32 = 1.0,
    f64 = 1.0,
);
