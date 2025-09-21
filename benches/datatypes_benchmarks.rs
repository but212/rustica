use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    pub mod choice;
    pub mod cont;
    pub mod either;
    pub mod id;
    pub mod io;
    pub mod iso_lens;
    pub mod iso_prism;
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
use datatypes::choice::choice_benchmarks;
use datatypes::cont::cont_benchmarks;
use datatypes::either::either_benchmarks;
use datatypes::id::id_benchmarks;
use datatypes::io::io_benchmarks;
use datatypes::iso_lens::iso_lens_benchmarks;
use datatypes::iso_prism::iso_prism_benchmarks;
use datatypes::lens::lens_benchmarks;
use datatypes::maybe::maybe_benchmarks;
use datatypes::prism::prism_benchmarks;
use datatypes::pvec::pvec_benchmarks;
use datatypes::reader::reader_benchmarks;
use datatypes::state::state_benchmarks;
use datatypes::validated::validated_benchmarks;
use datatypes::writer::writer_benchmarks;

criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    state_benchmarks,
    validated_benchmarks,
    choice_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    either_benchmarks,
    id_benchmarks,
    cont_benchmarks,
    io_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    iso_lens_benchmarks,
    iso_prism_benchmarks,
    pvec_benchmarks,
);

criterion_main!(datatype_benches);
