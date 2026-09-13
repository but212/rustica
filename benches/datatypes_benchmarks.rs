#[path = "support/harness.rs"]
pub mod harness;

use harness::Harness;

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

fn main() {
    let harness = Harness::new();

    validated_benchmarks(&harness);
    io_benchmarks(&harness);
    lens_benchmarks(&harness);
    composable_error_benchmarks(&harness);
    lazy_error_benchmarks(&harness);

    #[cfg(feature = "pvec")]
    pvec_benchmarks(&harness);

    #[cfg(feature = "async")]
    asyncm_benchmarks(&harness);
}
