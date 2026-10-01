#[path = "support/harness.rs"]
pub mod harness;

use harness::{Harness, TrackingAllocator};

#[global_allocator]
static GLOBAL: TrackingAllocator = TrackingAllocator;

mod datatypes {
    pub mod choice;
    pub mod context_error;
    pub mod free;
    pub mod lens;
    pub mod monad_comparison;
    pub mod operational;
    pub mod prism;
    pub mod validated;
}

use datatypes::choice::choice_benchmarks;
use datatypes::context_error::context_error_benchmarks;
use datatypes::free::free_benchmarks;
use datatypes::lens::lens_benchmarks;
use datatypes::monad_comparison::monad_comparison_benchmarks;
use datatypes::operational::operational_benchmarks;
use datatypes::prism::prism_benchmarks;
use datatypes::validated::validated_benchmarks;

fn main() {
    let harness = Harness::new();

    validated_benchmarks(&harness);
    lens_benchmarks(&harness);
    prism_benchmarks(&harness);
    free_benchmarks(&harness);
    operational_benchmarks(&harness);
    choice_benchmarks(&harness);
    monad_comparison_benchmarks(&harness);
    context_error_benchmarks(&harness);
}
