#!/bin/bash

# PersistentVector Performance Benchmark Execution Script
# 
# This script benchmarks various performance aspects of PersistentVector:
# 1. Basic operation performance
# 2. Size-based performance characteristics
# 3. Cache policy comparison
# 4. Memory efficiency
# 5. Performance comparison with std::Vec
# 6. Concurrency performance
# 7. Structural sharing efficiency

set -e

echo "PersistentVector benchmark starting..."
echo "=================================="

# Create benchmark results directory
BENCHMARK_DIR="target/criterion"
mkdir -p "$BENCHMARK_DIR"

# Results filename with current timestamp
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_FILE="pvec_benchmark_results_${TIMESTAMP}.txt"

echo "Benchmark results will be saved to: $BENCHMARK_DIR/$RESULTS_FILE"
echo ""

# Run benchmarks with pvec feature enabled
echo "Running benchmarks with pvec feature..."
cargo bench --features pvec --bench datatypes_benchmarks 2>&1 | tee "$BENCHMARK_DIR/$RESULTS_FILE"

echo ""
echo "Benchmark completed!"
echo ""

# Generate results summary
echo "Generating benchmark results summary..."
echo "================================" >> "$BENCHMARK_DIR/$RESULTS_FILE"
echo "Benchmark completion time: $(date)" >> "$BENCHMARK_DIR/$RESULTS_FILE"
echo "Rust version: $(rustc --version)" >> "$BENCHMARK_DIR/$RESULTS_FILE"
echo "Cargo version: $(cargo --version)" >> "$BENCHMARK_DIR/$RESULTS_FILE"

# Extract key performance metrics (simple grep-based)
echo "" >> "$BENCHMARK_DIR/$RESULTS_FILE"
echo "=== Key Performance Metrics ===" >> "$BENCHMARK_DIR/$RESULTS_FILE"

# Extract PersistentVector vs std::Vec comparison results
if grep -q "pvec_vs_vec" "$BENCHMARK_DIR/$RESULTS_FILE"; then
    echo "PersistentVector vs std::Vec performance comparison:" >> "$BENCHMARK_DIR/$RESULTS_FILE"
    grep "pvec_vs_vec" "$BENCHMARK_DIR/$RESULTS_FILE" | head -10 >> "$BENCHMARK_DIR/$RESULTS_FILE"
fi

# Extract cache policy comparison results
if grep -q "pvec_cache_policy" "$BENCHMARK_DIR/$RESULTS_FILE"; then
    echo "" >> "$BENCHMARK_DIR/$RESULTS_FILE"
    echo "Cache policy performance comparison:" >> "$BENCHMARK_DIR/$RESULTS_FILE"
    grep "pvec_cache_policy" "$BENCHMARK_DIR/$RESULTS_FILE" | head -10 >> "$BENCHMARK_DIR/$RESULTS_FILE"
fi

echo ""
echo "Benchmark results summary:"
echo "- Full results: $BENCHMARK_DIR/$RESULTS_FILE"
echo "- Criterion HTML report: $BENCHMARK_DIR/report/index.html"
echo ""

# Check if HTML report was generated
if [ -f "$BENCHMARK_DIR/report/index.html" ]; then
    echo "To view HTML report in browser:"
    echo "   file://$(pwd)/$BENCHMARK_DIR/report/index.html"
else
    echo "HTML report was not generated. Please check Criterion configuration."
fi

echo ""
echo "Performance target achievement check:"
echo "- Is PersistentVector access speed within 2x of Vec?"
echo "- Is memory usage within 1.5x compared to functional data structures?"
echo "- Is structural sharing working efficiently?"
echo ""
echo "Please check the generated reports for detailed analysis."
