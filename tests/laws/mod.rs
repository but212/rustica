#[macro_export]
macro_rules! test_functor_laws {
    ($mod_name:ident, $type:ty, $inner_type:ty, $f:expr, $g:expr) => {
        mod $mod_name {
            use super::*;

            #[quickcheck]
            fn functor_identity(x: $type) -> bool {
                // Law: fmap id = id
                x.fmap(|a: &$inner_type| a.clone()) == x
            }

            #[quickcheck]
            fn functor_composition(x: $type) -> bool {
                let f = $f;
                let g = $g;
                // fmap (g . f) = fmap g . fmap f
                let h = |a: &$inner_type| g(&f(a));
                x.fmap(h) == x.fmap(f).fmap(g)
            }
        }
    };
}
