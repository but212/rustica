//! # One Trait
//!
//! Multiplicative identity element for types that support multiplication.

/// A type that has a multiplicative identity value.
///
/// Implementors must guarantee that `x * T::one() == x` and
/// `T::one() * x == x` hold for every `x: T`.
pub trait One: Sized {
    /// Returns `1`, the identity value for multiplication on `Self`.
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
