use crate::fntype::SendSyncFnTrait;
use crate::category::hkt::ReturnTypeConstraints;

/// A bifunctor is a type constructor that provides a way to map a function over its contents.
///
/// # Type Parameters
/// * `A` - The type of the first content
/// * `B` - The type of the second content
///
/// # Laws
/// - Left Identity: `bimap(duplicate(w), f) = w`
/// - Right Identity: `bimap(f, duplicate(w)) = w`
/// - Associativity: `bimap(f, g)(w) = bimap(f, g)(bimap(f, g)(w))`
///
/// # Examples
///
/// ```
/// use rustica::category::bifunctor::Bifunctor;
/// use rustica::prelude::ReturnTypeConstraints;
/// use rustica::fntype::{SendSyncFnTrait, SendSyncFn};
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct MyBifunctor<A, B> {
///     left: A,
///     right: B,
/// }
///
/// impl<A, B> Bifunctor<A, B> for MyBifunctor<A, B>
/// where
///     A: ReturnTypeConstraints,
///     B: ReturnTypeConstraints,
/// {
///     type Output<C, D> = MyBifunctor<C, D>
///     where
///         C: ReturnTypeConstraints,
///         D: ReturnTypeConstraints;
///
///     fn first<C, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<C, B>
///     where
///         C: ReturnTypeConstraints,
///         F: SendSyncFnTrait<A, C>,
///     {
///         MyBifunctor {
///             left: f.call(self.left),
///             right: self.right,
///         }
///     }
///
///     fn second<D, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<A, D>
///     where
///         D: ReturnTypeConstraints,
///         F: SendSyncFnTrait<B, D>,
///     {
///         MyBifunctor {
///             left: self.left,
///             right: f.call(self.right),
///         }
///     }
///
///     fn bimap<C, D, F, G>(self, f: F, g: G) -> <Self as Bifunctor<A, B>>::Output<C, D>
///     where
///         C: ReturnTypeConstraints,
///         D: ReturnTypeConstraints,
///         F: SendSyncFnTrait<A, C>,
///         G: SendSyncFnTrait<B, D>,
///     {
///         MyBifunctor {
///             left: f.call(self.left),
///             right: g.call(self.right),
///         }
///     }
/// }
///
/// let bifunctor = MyBifunctor { left: 1, right: "hello" };
/// let mapped = bifunctor.bimap(SendSyncFn::new(|x| x + 1), SendSyncFn::new(|y:&str| y.len()));
/// assert_eq!(mapped.left, 2);
/// assert_eq!(mapped.right, 5);
/// ```
pub trait Bifunctor<A, B>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// The type constructor for the output of the bifunctor operation.
    ///
    /// # Type Parameters
    /// * `C` - The first type parameter of the output.
    /// * `D` - The second type parameter of the output.
    type Output<C, D>: Bifunctor<C, D> 
    where
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints;

    /// Maps a function over the first type parameter.
    ///
    /// # Arguments
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `A` and returns a value of type `C`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the function `f` to the first type parameter.
    ///
    /// # Type Parameters
    /// - `C`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `C`.
    fn first<C, F>(self, f: F) -> Self::Output<C, B>
    where
        C: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, C>;

    /// Maps a function over the second type parameter.
    ///
    /// # Arguments
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `B` and returns a value of type `D`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the function `f` to the second type parameter.
    ///
    /// # Type Parameters
    /// - `D`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `B` and returns a value of type `D`.
    fn second<D, F>(self, f: F) -> Self::Output<A, D>
    where
        D: ReturnTypeConstraints,
        F: SendSyncFnTrait<B, D>;

    /// Maps two functions over both type parameters simultaneously.
    ///
    /// # Arguments
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `A` and returns a value of type `C`.
    /// - `g`: A function that takes a value of type `B` and returns a value of type `D`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the functions `f` and `g` to the type parameters.
    ///
    /// # Type Parameters
    /// - `C`: The return type of the function `f`.
    /// - `D`: The return type of the function `g`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `C`.
    /// - `G`: A function type that takes a value of type `B` and returns a value of type `D`.
    fn bimap<C, D, F, G>(self, f: F, g: G) -> Self::Output<C, D>
    where
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, C>,
        G: SendSyncFnTrait<B, D>;
}
