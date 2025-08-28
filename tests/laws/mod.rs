#[macro_export]
macro_rules! test_functor_laws {
    ($type:ty) => {
        #[quickcheck]
        fn functor_identity(x: $type) -> bool {
            // Law: fmap id = id
            x.fmap(|a: &i32| *a) == x
        }

        #[quickcheck]
        fn functor_composition(x: $type) -> bool {
            let f = |a: &i32| a.saturating_add(1);
            let g = |a: &i32| a.saturating_mul(2);
            // fmap (g . f) = fmap g . fmap f
            let h = |a: &i32| g(&f(a));
            x.fmap(h) == x.fmap(f).fmap(g)
        }
    };
}
