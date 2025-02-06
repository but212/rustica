use crate::fntype::SendSyncFn;
use crate::fntype::SendSyncFnTrait;
use crate::category::hkt::ReturnTypeConstraints;

pub trait Composable {
    fn compose<T, U, V, F, G>(f: F, g: G) -> SendSyncFn<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
        G: SendSyncFnTrait<U, V>,
    {
        SendSyncFn::new(move |x: T| g.call(f.call(x)))
    }
}
