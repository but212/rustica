use criterion::{criterion_group, criterion_main};

mod datatypes {
    #[cfg(feature = "async")]
    pub mod async_monad;
    pub mod composable_error;
    pub mod io;
    pub mod lazy_error;
    pub mod lens;
    #[cfg(feature = "pvec")]
    pub mod pvec;
    pub mod validated;
}

#[cfg(feature = "async")]
use datatypes::async_monad::asyncm_benchmarks;
use datatypes::composable_error::composable_error_benchmarks;
use datatypes::io::io_benchmarks;
use datatypes::lazy_error::lazy_error_benchmarks;
use datatypes::lens::lens_benchmarks;
#[cfg(feature = "pvec")]
use datatypes::pvec::pvec_benchmarks;
use datatypes::validated::validated_benchmarks;

#[cfg(all(not(feature = "async"), not(feature = "pvec")))]
criterion_group!(
    datatype_benches,
    validated_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
);

#[cfg(all(not(feature = "async"), feature = "pvec"))]
criterion_group!(
    datatype_benches,
    validated_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    pvec_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
);

#[cfg(all(feature = "async", not(feature = "pvec")))]
criterion_group!(
    datatype_benches,
    validated_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
    asyncm_benchmarks,
);

#[cfg(all(feature = "async", feature = "pvec"))]
criterion_group!(
    datatype_benches,
    validated_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    pvec_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
    asyncm_benchmarks,
);

criterion_main!(datatype_benches);
