use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    #[cfg(feature = "async")]
    pub mod async_monad;
    pub mod choice;
    pub mod composable_error;
    pub mod cont;
    pub mod id;
    pub mod io;
    pub mod lazy_error;
    pub mod lens;
    pub mod prism;
    pub mod pvec;
    pub mod reader;
    pub mod state;
    pub mod validated;
    pub mod writer;
}

// Re-export benchmark functions
#[cfg(feature = "async")]
use datatypes::async_monad::asyncm_benchmarks;
use datatypes::choice::choice_benchmarks;
use datatypes::composable_error::composable_error_benchmarks;
use datatypes::cont::cont_benchmarks;
use datatypes::id::id_benchmarks;
use datatypes::io::io_benchmarks;
use datatypes::lazy_error::lazy_error_benchmarks;
use datatypes::lens::lens_benchmarks;
use datatypes::prism::prism_benchmarks;
use datatypes::pvec::pvec_benchmarks;
use datatypes::reader::reader_benchmarks;
use datatypes::state::state_benchmarks;
use datatypes::validated::validated_benchmarks;
use datatypes::writer::writer_benchmarks;

#[cfg(not(feature = "async"))]
criterion_group!(
    datatype_benches,
    state_benchmarks,
    validated_benchmarks,
    choice_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    id_benchmarks,
    cont_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    pvec_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
);

#[cfg(feature = "async")]
criterion_group!(
    datatype_benches,
    state_benchmarks,
    validated_benchmarks,
    choice_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    id_benchmarks,
    cont_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    pvec_benchmarks,
    composable_error_benchmarks,
    lazy_error_benchmarks,
    asyncm_benchmarks,
);

criterion_main!(datatype_benches);
