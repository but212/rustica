#[macro_export]
macro_rules! test_functor_laws {
    ($mod_name:ident, $type:ty, $f:expr, $g:expr) => {
        mod $mod_name {
            use super::*;

            #[quickcheck]
            fn functor_identity(x: $type) -> bool {
                // Law: fmap id = id
                x.clone().fmap(|a| a) == x
            }

            #[quickcheck]
            fn functor_composition(x: $type) -> bool {
                let f = $f;
                let g = $g;
                let f2 = f;
                let g2 = g;
                // Law: fmap (g . f) = fmap g . fmap f
                x.clone().fmap(move |a| g(f(a))) == x.fmap(f2).fmap(g2)
            }
        }
    };
}
