use criterion::{criterion_group, criterion_main};

// Import benchmark modules
mod datatypes {
    pub mod maybe;
    #[cfg(feature = "pvec")]
    pub mod pvec;
    pub mod state;
    pub mod validated;
}

// Re-export benchmark functions
use datatypes::maybe::maybe_benchmarks;
#[cfg(feature = "pvec")]
use datatypes::pvec::pvec_benchmarks;
use datatypes::state::state_benchmarks;
use datatypes::validated::validated_benchmarks;

#[cfg(not(feature = "pvec"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    state_benchmarks,
    validated_benchmarks,
);

#[cfg(feature = "pvec")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    pvec_benchmarks,
    state_benchmarks,
    validated_benchmarks,
);

criterion_main!(datatype_benches);
