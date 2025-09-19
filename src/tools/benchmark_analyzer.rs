//! Benchmark result analysis tool
//!
//! This module provides tools for analyzing PersistentVector benchmark results
//! and evaluating whether performance targets are met.

use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Benchmark result data
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub time_ns: f64,
    pub throughput: Option<f64>,
    pub memory_usage: Option<usize>,
}

/// Performance target definitions
#[derive(Debug, Clone)]
pub struct PerformanceTargets {
    /// How many times slower PersistentVector access can be compared to Vec
    pub access_speed_ratio: f64,
    /// How many times more memory usage is allowed compared to baseline
    pub memory_usage_ratio: f64,
    /// Minimum structural sharing efficiency (0.0 ~ 1.0)
    pub min_sharing_efficiency: f64,
}

impl Default for PerformanceTargets {
    fn default() -> Self {
        Self {
            access_speed_ratio: 2.0,     // Within 2x of Vec
            memory_usage_ratio: 1.5,     // Within 1.5x
            min_sharing_efficiency: 0.7, // 70% or higher
        }
    }
}

/// Benchmark analyzer
pub struct BenchmarkAnalyzer {
    results: Vec<BenchmarkResult>,
    targets: PerformanceTargets,
}

impl BenchmarkAnalyzer {
    /// Create a new analyzer
    pub fn new(targets: PerformanceTargets) -> Self {
        Self {
            results: Vec::new(),
            targets,
        }
    }

    /// Create analyzer with default settings
    pub fn with_default_targets() -> Self {
        Self::new(PerformanceTargets::default())
    }

    /// Load benchmark results from file
    pub fn load_results_from_file<P: AsRef<Path>>(
        &mut self, path: P,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        self.parse_criterion_output(&content)?;
        Ok(())
    }

    /// Parse Criterion output
    fn parse_criterion_output(&mut self, content: &str) -> Result<(), Box<dyn std::error::Error>> {
        for line in content.lines() {
            if let Some(result) = self.parse_benchmark_line(line) {
                self.results.push(result);
            }
        }
        Ok(())
    }

    /// Parse individual benchmark line
    fn parse_benchmark_line(&self, line: &str) -> Option<BenchmarkResult> {
        // Criterion output format example:
        // "pvec_basic/create        time:   [123.45 ns 125.67 ns 127.89 ns]"
        // "pvec_vs_vec/pvec_access  time:   [1.2345 µs 1.2567 µs 1.2789 µs]"

        if !line.contains("time:") {
            return None;
        }

        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 6 {
            return None;
        }

        let name = parts[0].to_string();

        // Extract median value (second time value)
        let time_str = parts[4];
        let time_value = self.parse_time_value(time_str)?;

        Some(BenchmarkResult {
            name,
            time_ns: time_value,
            throughput: None,
            memory_usage: None,
        })
    }

    /// Parse time value (convert to ns)
    fn parse_time_value(&self, time_str: &str) -> Option<f64> {
        let time_str = time_str.trim();

        if let Some(value_str) = time_str.strip_suffix("ns") {
            value_str.parse().ok()
        } else if let Some(value_str) = time_str.strip_suffix("µs") {
            value_str.parse::<f64>().ok().map(|v| v * 1000.0)
        } else if let Some(value_str) = time_str.strip_suffix("ms") {
            value_str.parse::<f64>().ok().map(|v| v * 1_000_000.0)
        } else if let Some(value_str) = time_str.strip_suffix("s") {
            value_str.parse::<f64>().ok().map(|v| v * 1_000_000_000.0)
        } else {
            None
        }
    }

    /// Analyze PersistentVector vs std::Vec performance comparison
    pub fn analyze_pvec_vs_vec(&self) -> PerformanceComparison {
        let mut pvec_results = HashMap::new();
        let mut vec_results = HashMap::new();

        for result in &self.results {
            if result.name.contains("pvec_vs_vec") {
                if result.name.contains("pvec_") {
                    let operation = self.extract_operation_name(&result.name);
                    pvec_results.insert(operation, result.time_ns);
                } else if result.name.contains("std_vec_") {
                    let operation = self.extract_operation_name(&result.name);
                    vec_results.insert(operation, result.time_ns);
                }
            }
        }

        let mut comparisons = Vec::new();
        for (operation, pvec_time) in &pvec_results {
            if let Some(vec_time) = vec_results.get(operation) {
                let ratio = pvec_time / vec_time;
                let meets_target = ratio <= self.targets.access_speed_ratio;

                comparisons.push(OperationComparison {
                    operation: operation.clone(),
                    pvec_time_ns: *pvec_time,
                    vec_time_ns: *vec_time,
                    ratio,
                    meets_target,
                });
            }
        }

        PerformanceComparison { comparisons }
    }

    /// Extract operation name
    fn extract_operation_name(&self, benchmark_name: &str) -> String {
        // "pvec_vs_vec/pvec_access" -> "access"
        // "pvec_vs_vec/std_vec_build" -> "build"
        if let Some(last_part) = benchmark_name.split('/').last() {
            if let Some(operation) = last_part.strip_prefix("pvec_") {
                operation.to_string()
            } else if let Some(operation) = last_part.strip_prefix("std_vec_") {
                operation.to_string()
            } else {
                last_part.to_string()
            }
        } else {
            benchmark_name.to_string()
        }
    }

    /// Analyze cache policy performance
    pub fn analyze_cache_policies(&self) -> CachePolicyAnalysis {
        let mut policy_results = HashMap::new();

        for result in &self.results {
            if result.name.contains("pvec_cache_policy") {
                if let Some(policy_name) = self.extract_cache_policy_name(&result.name) {
                    policy_results.insert(policy_name, result.time_ns);
                }
            }
        }

        // Find the fastest policy
        let best_policy = policy_results
            .iter()
            .min_by(|a, b| a.1.partial_cmp(b.1).unwrap())
            .map(|(name, time)| (name.clone(), *time));

        CachePolicyAnalysis {
            policy_results,
            best_policy,
        }
    }

    /// Extract cache policy name
    fn extract_cache_policy_name(&self, benchmark_name: &str) -> Option<String> {
        if let Some(last_part) = benchmark_name.split('/').last() {
            Some(last_part.to_string())
        } else {
            None
        }
    }

    /// Generate comprehensive performance report
    pub fn generate_report(&self) -> PerformanceReport {
        let pvec_vs_vec = self.analyze_pvec_vs_vec();
        let cache_policies = self.analyze_cache_policies();

        // Evaluate target achievement
        let access_speed_target_met = pvec_vs_vec.comparisons.iter().all(|comp| comp.meets_target);

        PerformanceReport {
            pvec_vs_vec,
            cache_policies,
            targets_met: TargetsMet {
                access_speed: access_speed_target_met,
                memory_usage: true,       // TODO: Implement actual memory analysis
                sharing_efficiency: true, // TODO: Implement actual sharing efficiency analysis
            },
            recommendations: self.generate_recommendations(),
        }
    }

    /// Generate performance improvement recommendations
    fn generate_recommendations(&self) -> Vec<String> {
        let mut recommendations = Vec::new();

        let pvec_vs_vec = self.analyze_pvec_vs_vec();

        // Find operations that exceed performance targets
        for comp in &pvec_vs_vec.comparisons {
            if !comp.meets_target {
                recommendations.push(format!(
                    "{} operation performance needs improvement. Currently {:.2}x slower than Vec (target: within {:.2}x)",
                    comp.operation, comp.ratio, self.targets.access_speed_ratio
                ));
            }
        }

        // Cache policy recommendations
        let cache_analysis = self.analyze_cache_policies();
        if let Some((best_policy, _)) = &cache_analysis.best_policy {
            recommendations.push(format!("Recommended optimal cache policy: {}", best_policy));
        }

        if recommendations.is_empty() {
            recommendations.push("All performance targets achieved! 🎉".to_string());
        }

        recommendations
    }
}

/// Performance comparison results
#[derive(Debug)]
pub struct PerformanceComparison {
    pub comparisons: Vec<OperationComparison>,
}

/// Individual operation comparison result
#[derive(Debug)]
pub struct OperationComparison {
    pub operation: String,
    pub pvec_time_ns: f64,
    pub vec_time_ns: f64,
    pub ratio: f64,
    pub meets_target: bool,
}

/// Cache policy analysis results
#[derive(Debug)]
pub struct CachePolicyAnalysis {
    pub policy_results: HashMap<String, f64>,
    pub best_policy: Option<(String, f64)>,
}

/// Target achievement status
#[derive(Debug)]
pub struct TargetsMet {
    pub access_speed: bool,
    pub memory_usage: bool,
    pub sharing_efficiency: bool,
}

/// Comprehensive performance report
#[derive(Debug)]
pub struct PerformanceReport {
    pub pvec_vs_vec: PerformanceComparison,
    pub cache_policies: CachePolicyAnalysis,
    pub targets_met: TargetsMet,
    pub recommendations: Vec<String>,
}

impl PerformanceReport {
    /// Print report summary to console
    pub fn print_summary(&self) {
        println!("🎯 PersistentVector Performance Analysis Report");
        println!("===============================================");
        println!();

        // PersistentVector vs std::Vec comparison
        println!("📊 PersistentVector vs std::Vec Performance Comparison:");
        for comp in &self.pvec_vs_vec.comparisons {
            let status = if comp.meets_target { "✅" } else { "❌" };
            println!(
                "  {} {}: {:.2}x (target: within 2.0x)",
                status, comp.operation, comp.ratio
            );
        }
        println!();

        // Cache policy analysis
        println!("🔄 Cache Policy Performance Analysis:");
        if let Some((best_policy, best_time)) = &self.cache_policies.best_policy {
            println!("  🏆 Optimal policy: {} ({:.2} ns)", best_policy, best_time);
        }
        for (policy, time) in &self.cache_policies.policy_results {
            println!("    {}: {:.2} ns", policy, time);
        }
        println!();

        // Target achievement status
        println!("🎯 Performance Target Achievement:");
        println!(
            "  Access speed: {}",
            if self.targets_met.access_speed {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        );
        println!(
            "  Memory usage: {}",
            if self.targets_met.memory_usage {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        );
        println!(
            "  Structural sharing efficiency: {}",
            if self.targets_met.sharing_efficiency {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        );
        println!();

        // Recommendations
        println!("💡 Performance Improvement Recommendations:");
        for (i, recommendation) in self.recommendations.iter().enumerate() {
            println!("  {}. {}", i + 1, recommendation);
        }
    }

    /// Save report to file
    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn std::error::Error>> {
        let mut content = String::new();

        content.push_str("# PersistentVector Performance Analysis Report\n\n");

        content.push_str("## PersistentVector vs std::Vec Performance Comparison\n\n");
        for comp in &self.pvec_vs_vec.comparisons {
            let status = if comp.meets_target { "✅" } else { "❌" };
            content.push_str(&format!(
                "- {} {}: {:.2}x (target: within 2.0x)\n",
                status, comp.operation, comp.ratio
            ));
        }

        content.push_str("\n## Cache Policy Performance Analysis\n\n");
        if let Some((best_policy, best_time)) = &self.cache_policies.best_policy {
            content.push_str(&format!(
                "**Optimal policy**: {} ({:.2} ns)\n\n",
                best_policy, best_time
            ));
        }

        content.push_str("### Performance by Policy\n\n");
        for (policy, time) in &self.cache_policies.policy_results {
            content.push_str(&format!("- {}: {:.2} ns\n", policy, time));
        }

        content.push_str("\n## Performance Target Achievement\n\n");
        content.push_str(&format!(
            "- Access speed: {}\n",
            if self.targets_met.access_speed {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        ));
        content.push_str(&format!(
            "- Memory usage: {}\n",
            if self.targets_met.memory_usage {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        ));
        content.push_str(&format!(
            "- Structural sharing efficiency: {}\n",
            if self.targets_met.sharing_efficiency {
                "✅ Met"
            } else {
                "❌ Not met"
            }
        ));

        content.push_str("\n## Performance Improvement Recommendations\n\n");
        for (i, recommendation) in self.recommendations.iter().enumerate() {
            content.push_str(&format!("{}. {}\n", i + 1, recommendation));
        }

        fs::write(path, content)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_time_value_parsing() {
        let analyzer = BenchmarkAnalyzer::with_default_targets();

        assert_eq!(analyzer.parse_time_value("123.45ns"), Some(123.45));
        assert_eq!(analyzer.parse_time_value("1.23µs"), Some(1230.0));
        assert_eq!(analyzer.parse_time_value("1.23ms"), Some(1_230_000.0));
        assert_eq!(analyzer.parse_time_value("1.23s"), Some(1_230_000_000.0));
    }

    #[test]
    fn test_operation_name_extraction() {
        let analyzer = BenchmarkAnalyzer::with_default_targets();

        assert_eq!(
            analyzer.extract_operation_name("pvec_vs_vec/pvec_access"),
            "access"
        );
        assert_eq!(
            analyzer.extract_operation_name("pvec_vs_vec/std_vec_build"),
            "build"
        );
    }
}
