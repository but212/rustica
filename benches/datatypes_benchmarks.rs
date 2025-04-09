use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    #[cfg(feature = "async")]
    pub mod async_monad;
    pub mod choice;
    pub mod cont;
    pub mod either;
    pub mod id;
    pub mod io;
    pub mod lens;
    pub mod maybe;
    pub mod prism;
    pub mod pvec;
    pub mod reader;
    pub mod state;
    pub mod validated;
    pub mod writer;
}

// Re-export benchmark functions
#[cfg(feature = "async")]
use datatypes::async_monad::async_monad_benchmarks;
use datatypes::choice::choice_benchmarks;
use datatypes::cont::cont_benchmarks;
use datatypes::either::either_benchmarks;
use datatypes::id::id_benchmarks;
use datatypes::io::io_benchmarks;
use datatypes::lens::lens_benchmarks;
use datatypes::maybe::maybe_benchmarks;
use datatypes::prism::prism_benchmarks;
use datatypes::pvec::pvec_benchmarks;
use datatypes::reader::reader_benchmarks;
use datatypes::state::state_benchmarks;
use datatypes::validated::validated_benchmarks;
use datatypes::writer::writer_benchmarks;

#[cfg(not(feature = "async"))]
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
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
    pvec_benchmarks,
);

#[cfg(feature = "async")]
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
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
    pvec_benchmarks,
);

criterion_main!(datatype_benches);
