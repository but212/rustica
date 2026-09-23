from __future__ import annotations

import sys
import tempfile
from pathlib import Path
from unittest import TestCase, main

SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

from release_metadata import Changelog, ReleaseEntry  # noqa: E402
from benchmark_report import BenchmarkEntry, BenchmarkReport, BenchmarkRunner  # noqa: E402


class ReleaseMetadataTests(TestCase):
    def test_dated_heading(self) -> None:
        changelog_text = "## [1.2.3] - 2026-08-20\n\n- Added feature\n\n## [1.2.2]"
        changelog = Changelog.from_markdown(changelog_text)
        entry = changelog.get_entry("1.2.3")

        self.assertEqual(
            entry,
            ReleaseEntry(
                version="1.2.3",
                date="2026-08-20",
                body="- Added feature",
            ),
        )

    def test_undated_heading(self) -> None:
        changelog_text = "## [1.2.3]\n\n- Fixed bug"
        changelog = Changelog.from_markdown(changelog_text)
        entry = changelog.get_entry("1.2.3")

        self.assertEqual(
            entry,
            ReleaseEntry(
                version="1.2.3",
                date=None,
                body="- Fixed bug",
            ),
        )

    def test_missing_heading_raises(self) -> None:
        changelog = Changelog.from_markdown("## [1.2.2]\n\n- Older")
        with self.assertRaisesRegex(ValueError, "No exact CHANGELOG entry found for 1.2.3"):
            changelog.get_entry("1.2.3")

    def test_empty_heading_raises(self) -> None:
        changelog_text = "## [1.2.3] - 2026-08-20\n\n## [1.2.2]"
        changelog = Changelog.from_markdown(changelog_text)
        with self.assertRaisesRegex(ValueError, "CHANGELOG entry for 1.2.3 is empty"):
            changelog.get_entry("1.2.3")

    def test_unicode_heading_and_body(self) -> None:
        unicode_body = "- Fixed: 2.3x–6.1x faster (n \u2265 1)"
        changelog_text = f"## [1.2.3] - 2026-08-20\n\n{unicode_body}\n\n## [1.2.2]"
        changelog = Changelog.from_markdown(changelog_text)

        self.assertEqual(changelog.extract_body("1.2.3"), unicode_body)

    def test_empty_body_instantiation_raises(self) -> None:
        with self.assertRaisesRegex(ValueError, "CHANGELOG entry for 1.2.3 is empty"):
            ReleaseEntry(version="1.2.3", body="", date="2026-08-20")

    def test_duplicate_version_keeps_first_entry(self) -> None:
        changelog_text = (
            "## [1.2.3] - 2026-08-20\n\n- Newer entry\n\n"
            "## [1.2.3] - 2026-08-19\n\n- Older entry"
        )
        changelog = Changelog.from_markdown(changelog_text)
        entry = changelog.get_entry("1.2.3")
        self.assertEqual(entry.body, "- Newer entry")


class BenchmarkReportTests(TestCase):
    def test_parse_entries_with_and_without_throughput(self) -> None:
        sample_output = """
Compiling rustica v0.17.0
Finished `bench` profile [optimized] target(s)
 Running benches/datatypes_benchmarks.rs
Validated/invalid_many/4                 ... mean:     212ns median:     210ns p95:     220ns min:     200ns max:     440ns (100 iters)
PersistentVector/pvec_push_back/64       ... mean:   8.335µs median:    8.21µs p95:    8.73µs min:    8.01µs max:   12.67µs (100 iters) [7.68 M elem/s]
Lens/set_same_value                      ... mean:     202ns min:     180ns max:     380ns (100 iters)
"""
        report = BenchmarkReport.from_raw_text(sample_output)
        self.assertEqual(len(report.entries), 3)

        self.assertEqual(
            report.entries[0],
            BenchmarkEntry(
                group="Validated",
                name="invalid_many/4",
                mean="212ns",
                median="210ns",
                p95="220ns",
                min="200ns",
                max="440ns",
                iters=100,
                throughput="-",
            ),
        )
        self.assertEqual(
            report.entries[1],
            BenchmarkEntry(
                group="PersistentVector",
                name="pvec_push_back/64",
                mean="8.335µs",
                median="8.21µs",
                p95="8.73µs",
                min="8.01µs",
                max="12.67µs",
                iters=100,
                throughput="7.68 M elem/s",
            ),
        )
        self.assertEqual(
            report.entries[2],
            BenchmarkEntry(
                group="Lens",
                name="set_same_value",
                mean="202ns",
                median="-",
                p95="-",
                min="180ns",
                max="380ns",
                iters=100,
                throughput="-",
            ),
        )

    def test_parse_empty_or_non_benchmark_output_raises(self) -> None:
        with self.assertRaisesRegex(ValueError, "No benchmark results found in input text"):
            BenchmarkReport.from_raw_text("Compiling rustica v0.17.0\nFinished bench profile\n")

    def test_render_markdown_report_structure(self) -> None:
        entries = [
            BenchmarkEntry(
                group="Validated",
                name="validated_map",
                mean="4ns",
                median="0ns",
                p95="10ns",
                min="0ns",
                max="10ns",
                iters=100,
                throughput="-",
            ),
            BenchmarkEntry(
                group="PersistentVector",
                name="pvec_push_back/64",
                mean="8.335µs",
                median="8.21µs",
                p95="8.73µs",
                min="8.01µs",
                max="12.67µs",
                iters=100,
                throughput="7.68 M elem/s",
            ),
        ]
        report = BenchmarkReport(entries=entries, title="Benchmark Results")
        markdown = report.to_markdown()

        self.assertIn("# Benchmark Results", markdown)
        self.assertIn("## Validated", markdown)
        self.assertIn("## PersistentVector", markdown)
        self.assertIn("| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |", markdown)
        self.assertIn("| `validated_map` | 4ns | 0ns | 10ns | 0ns | 10ns | 100 | - |", markdown)
        self.assertIn("| `pvec_push_back/64` | 8.335µs | 8.21µs | 8.73µs | 8.01µs | 12.67µs | 100 | 7.68 M elem/s |", markdown)

    def test_resolve_input_with_explicit_file(self) -> None:
        with tempfile.NamedTemporaryFile("w", delete=False, encoding="utf-8") as tmp:
            tmp.write("Validated/foo ... mean: 10ns min: 5ns max: 20ns (100 iters)\n")
            tmp_path = Path(tmp.name)

        try:
            runner = BenchmarkRunner(repo_dir=Path("."))
            content = runner.resolve_raw_output(input_path=tmp_path, force_run=False)
            self.assertIn("Validated/foo", content)
        finally:
            tmp_path.unlink(missing_ok=True)

    def test_resolve_input_missing_file_raises(self) -> None:
        runner = BenchmarkRunner(repo_dir=Path("."))
        with self.assertRaises(FileNotFoundError):
            runner.resolve_raw_output(input_path=Path("non_existent_file_xyz.txt"), force_run=False)

    def test_resolve_input_relative_path_from_different_repo_dir(self) -> None:
        with tempfile.NamedTemporaryFile("w", dir=".", delete=False, encoding="utf-8") as tmp:
            tmp.write("Validated/bar ... mean: 12ns min: 6ns max: 24ns (100 iters)\n")
            rel_path = Path(tmp.name).name

        try:
            # repo_dir points to another directory (e.g. .github), but input_path is relative to cwd
            runner = BenchmarkRunner(repo_dir=Path(".github"))
            content = runner.resolve_raw_output(input_path=Path(rel_path), force_run=False)
            self.assertIn("Validated/bar", content)
        finally:
            Path(rel_path).unlink(missing_ok=True)


if __name__ == "__main__":
    main()
