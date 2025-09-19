//! PersistentVector Benchmark Result Analysis Example
//!
//! This example demonstrates how to analyze benchmark results and generate a performance report.
//!
//! How to run:
//! ```bash
//! cargo run --example benchmark_analysis --features dev-tools
//! ```

#[cfg(feature = "dev-tools")]
use rustica::tools::{BenchmarkAnalyzer, PerformanceTargets};

#[cfg(feature = "dev-tools")]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔍 PersistentVector Benchmark Result Analysis");
    println!("=====================================");

    // Set performance targets
    let targets = PerformanceTargets {
        access_speed_ratio: 2.0,     // Within 2x of Vec
        memory_usage_ratio: 1.5,     // Within 1.5x
        min_sharing_efficiency: 0.7, // 70% or higher
    };

    let mut analyzer = BenchmarkAnalyzer::new(targets);

    // Path to benchmark results file
    let benchmark_results_path = "target/criterion/pvec_benchmark_results.txt";

    // Check if the result file exists
    if std::path::Path::new(benchmark_results_path).exists() {
        println!(
            "📊 Loading benchmark results file: {}",
            benchmark_results_path
        );

        // Load the result file
        match analyzer.load_results_from_file(benchmark_results_path) {
            Ok(_) => {
                println!("✅ Benchmark results loaded successfully");

                // Generate performance report
                let report = analyzer.generate_report();

                // Print report to console
                report.print_summary();

                // Save report to file
                let report_path = "target/criterion/performance_report.md";
                match report.save_to_file(report_path) {
                    Ok(_) => println!("📄 Performance report saved: {}", report_path),
                    Err(e) => eprintln!("❌ Failed to save report: {}", e),
                }
            },
            Err(e) => {
                eprintln!("❌ Failed to load benchmark results: {}", e);
                println!("💡 Please run the benchmark first:");
                println!("   cargo bench --features pvec --bench datatypes_benchmarks");
            },
        }
    } else {
        println!(
            "⚠️  Could not find benchmark results file: {}",
            benchmark_results_path
        );
        println!();
        println!("💡 Please run the benchmark first:");
        println!("   cargo bench --features pvec --bench datatypes_benchmarks");
        println!();
        println!("Or use the script:");
        println!("   bash scripts/run_pvec_benchmarks.sh");

        // Demonstrate analysis with sample data
        demonstrate_analysis();
    }

    Ok(())
}

#[cfg(feature = "dev-tools")]
fn demonstrate_analysis() {
    println!();
    println!("🎭 Demonstrating analysis with sample data:");
    println!("================================");

    use rustica::tools::BenchmarkResult;

    // Create sample benchmark results
    let sample_results = vec![
        BenchmarkResult {
            name: "pvec_vs_vec/pvec_access".to_string(),
            time_ns: 150.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_vs_vec/std_vec_access".to_string(),
            time_ns: 100.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_vs_vec/pvec_build".to_string(),
            time_ns: 2000.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_vs_vec/std_vec_build".to_string(),
            time_ns: 1200.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_cache_policy/always_cache".to_string(),
            time_ns: 120.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_cache_policy/never_cache".to_string(),
            time_ns: 180.0,
            throughput: None,
            memory_usage: None,
        },
        BenchmarkResult {
            name: "pvec_cache_policy/even_index_cache".to_string(),
            time_ns: 140.0,
            throughput: None,
            memory_usage: None,
        },
    ];

    // Add sample results to analyzer (not possible in practice due to private fields)
    // Instead, demonstrate results directly

    println!("📊 PersistentVector vs std::Vec Performance Comparison:");
    println!("  ✅ access: 1.50x (target: within 2.0x)");
    println!("  ✅ build: 1.67x (target: within 2.0x)");
    println!();

    println!("🔄 Cache Policy Performance Analysis:");
    println!("  🏆 Optimal policy: always_cache (120.0 ns)");
    println!("    always_cache: 120.0 ns");
    println!("    even_index_cache: 140.0 ns");
    println!("    never_cache: 180.0 ns");
    println!();

    println!("🎯 Performance Target Achievement:");
    println!("  Access speed: ✅ Met");
    println!("  Memory usage: ✅ Met");
    println!("  Structural sharing efficiency: ✅ Met");
    println!();

    println!("💡 Performance Improvement Recommendations:");
    println!("  1. All performance targets achieved! 🎉");
    println!("  2. Recommended optimal cache policy: always_cache.");
}

#[cfg(not(feature = "dev-tools"))]
fn main() {
    println!("❌ You must enable the 'dev-tools' feature to run this example.");
    println!("Run with the following command:");
    println!("cargo run --example benchmark_analysis --features dev-tools");
}
