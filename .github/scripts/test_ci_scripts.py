from __future__ import annotations

import sys
from pathlib import Path
from unittest import TestCase, main


SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

from release_metadata import extract_release_body  # noqa: E402
from benchmark_report import BenchmarkEntry, parse_benchmark_output, render_markdown_report  # noqa: E402


class ReleaseMetadataTests(TestCase):
    def test_dated_heading(self) -> None:
        changelog = "## [1.2.3] - 2026-08-20\n\n- Added feature\n\n## [1.2.2]"
        self.assertEqual(extract_release_body("1.2.3", changelog), "- Added feature")

    def test_undated_heading(self) -> None:
        self.assertEqual(extract_release_body("1.2.3", "## [1.2.3]\n\n- Fixed bug"), "- Fixed bug")

    def test_missing_heading(self) -> None:
        with self.assertRaisesRegex(ValueError, "No exact"):
            extract_release_body("1.2.3", "## [1.2.2]\n\n- Older")

    def test_empty_heading(self) -> None:
        with self.assertRaisesRegex(ValueError, "empty"):
            extract_release_body("1.2.3", "## [1.2.3] - 2026-08-20\n\n## [1.2.2]")


class BenchmarkReportTests(TestCase):
    def test_parse_entries_with_and_without_throughput(self) -> None:
        sample_output = """
Compiling rustica v0.17.0
Finished `bench` profile [optimized] target(s)
 Running benches/datatypes_benchmarks.rs
Validated/invalid_many/4                 ... mean:      248ns min:      200ns max:      3.1µs (100 iters)
PersistentVector/pvec_push_back/64       ... mean:    9.238µs min:      7.2µs max:     28.8µs (100 iters) [6.93 M elem/s]
Lens/set_same_value                      ... mean:      226ns min:      100ns max:      1.5µs (100 iters)
"""
        entries = parse_benchmark_output(sample_output)
        self.assertEqual(len(entries), 3)

        self.assertEqual(
            entries[0],
            BenchmarkEntry(
                group="Validated",
                name="invalid_many/4",
                mean="248ns",
                min="200ns",
                max="3.1µs",
                iters=100,
                throughput="-",
            ),
        )
        self.assertEqual(
            entries[1],
            BenchmarkEntry(
                group="PersistentVector",
                name="pvec_push_back/64",
                mean="9.238µs",
                min="7.2µs",
                max="28.8µs",
                iters=100,
                throughput="6.93 M elem/s",
            ),
        )
        self.assertEqual(
            entries[2],
            BenchmarkEntry(
                group="Lens",
                name="set_same_value",
                mean="226ns",
                min="100ns",
                max="1.5µs",
                iters=100,
                throughput="-",
            ),
        )

    def test_parse_empty_or_non_benchmark_output_raises(self) -> None:
        with self.assertRaisesRegex(ValueError, "No benchmark results found"):
            parse_benchmark_output("Compiling rustica v0.17.0\nFinished bench profile\n")

    def test_render_markdown_report_structure(self) -> None:
        entries = [
            BenchmarkEntry(
                group="Validated",
                name="validated_map",
                mean="77ns",
                min="0ns",
                max="3µs",
                iters=100,
                throughput="-",
            ),
            BenchmarkEntry(
                group="PersistentVector",
                name="pvec_push_back/64",
                mean="9.238µs",
                min="7.2µs",
                max="28.8µs",
                iters=100,
                throughput="6.93 M elem/s",
            ),
        ]
        markdown = render_markdown_report(entries, title="Benchmark Results")
        self.assertIn("# Benchmark Results", markdown)
        self.assertIn("## Validated", markdown)
        self.assertIn("## PersistentVector", markdown)
        self.assertIn("| Benchmark | Mean | Min | Max | Iterations | Throughput |", markdown)
        self.assertIn("| `validated_map` | 77ns | 0ns | 3µs | 100 | - |", markdown)
        self.assertIn("| `pvec_push_back/64` | 9.238µs | 7.2µs | 28.8µs | 100 | 6.93 M elem/s |", markdown)

    def test_resolve_input_with_explicit_file(self) -> None:
        from benchmark_report import resolve_input
        import tempfile

        with tempfile.NamedTemporaryFile("w", delete=False, encoding="utf-8") as tmp:
            tmp.write("Validated/foo ... mean: 10ns min: 5ns max: 20ns (100 iters)\n")
            tmp_path = Path(tmp.name)

        try:
            content = resolve_input(Path("."), input_path=tmp_path, force_run=False)
            self.assertIn("Validated/foo", content)
        finally:
            tmp_path.unlink(missing_ok=True)

    def test_resolve_input_missing_file_raises(self) -> None:
        from benchmark_report import resolve_input

        with self.assertRaises(FileNotFoundError):
            resolve_input(Path("."), input_path=Path("non_existent_file_xyz.txt"), force_run=False)


if __name__ == "__main__":
    main()

