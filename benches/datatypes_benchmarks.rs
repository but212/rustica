#![allow(deprecated)]

#[path = "support/harness.rs"]
pub mod harness;

use harness::{Harness, TrackingAllocator};

#[global_allocator]
static GLOBAL: TrackingAllocator = TrackingAllocator;

mod datatypes {
    pub mod composable_error;
    pub mod lazy_error;
    pub mod lens;
    #[cfg(feature = "pvec")]
    pub mod pvec;
    pub mod validated;
}

use datatypes::composable_error::composable_error_benchmarks;
use datatypes::lazy_error::lazy_error_benchmarks;
use datatypes::lens::lens_benchmarks;
#[cfg(feature = "pvec")]
use datatypes::pvec::pvec_benchmarks;
use datatypes::validated::validated_benchmarks;

fn main() {
    let harness = Harness::new();

    validated_benchmarks(&harness);
    lens_benchmarks(&harness);
    composable_error_benchmarks(&harness);
    lazy_error_benchmarks(&harness);

    #[cfg(feature = "pvec")]
    pvec_benchmarks(&harness);
}
