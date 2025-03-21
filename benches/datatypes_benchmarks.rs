use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    #[cfg(feature = "async")]
    pub mod async_monad;
    #[cfg(feature = "advanced")]
    pub mod choice;
    #[cfg(feature = "advanced")]
    pub mod cont;
    pub mod either;
    pub mod id;
    #[cfg(feature = "advanced")]
    pub mod io;
    pub mod lens;
    pub mod maybe;
    pub mod prism;
    pub mod reader;
    #[cfg(feature = "advanced")]
    pub mod state;
    pub mod validated;
    pub mod wrapper;
    pub mod writer;
}

// Re-export benchmark functions
use datatypes::either::either_benchmarks;
use datatypes::id::id_benchmarks;
use datatypes::lens::lens_benchmarks;
use datatypes::maybe::maybe_benchmarks;
use datatypes::prism::prism_benchmarks;
use datatypes::reader::reader_benchmarks;
use datatypes::validated::validated_benchmarks;
use datatypes::wrapper::wrapper_benchmarks;
use datatypes::writer::writer_benchmarks;

#[cfg(feature = "async")]
use datatypes::async_monad::async_monad_benchmarks;
#[cfg(feature = "advanced")]
use datatypes::choice::choice_benchmarks;
#[cfg(feature = "advanced")]
use datatypes::cont::cont_benchmarks;
#[cfg(feature = "advanced")]
use datatypes::io::io_benchmarks;
#[cfg(feature = "advanced")]
use datatypes::state::state_benchmarks;

// Configure criterion groups for different feature combinations
#[cfg(not(feature = "async"))]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    async_monad_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(not(feature = "async"))]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
    io_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    async_monad_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
    io_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

criterion_main!(datatype_benches);
