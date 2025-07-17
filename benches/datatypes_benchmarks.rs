use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    pub mod choice;
    pub mod either;
    pub mod id;
    pub mod maybe;
    #[cfg(feature = "pvec")]
    pub mod pvec;
    pub mod reader;
    pub mod state;
    pub mod validated;
    pub mod writer;
}

// Re-export benchmark functions
use datatypes::choice::choice_benchmarks;
use datatypes::either::either_benchmarks;
use datatypes::id::id_benchmarks;
use datatypes::maybe::maybe_benchmarks;
#[cfg(feature = "pvec")]
use datatypes::pvec::pvec_benchmarks;
use datatypes::reader::reader_benchmarks;
use datatypes::state::state_benchmarks;
use datatypes::validated::validated_benchmarks;
use datatypes::writer::writer_benchmarks;

#[cfg(not(feature = "pvec"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    state_benchmarks,
    validated_benchmarks,
    choice_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    either_benchmarks,
    id_benchmarks
);

#[cfg(feature = "pvec")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    state_benchmarks,
    validated_benchmarks,
    choice_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    pvec_benchmarks,
    either_benchmarks,
    id_benchmarks
);

criterion_main!(datatype_benches);
