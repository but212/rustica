from __future__ import annotations

import io
import os
import sys
from pathlib import Path
from unittest import TestCase, main
from unittest.mock import patch
from urllib.error import HTTPError


SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

from benchmark_common import api, parse_results  # noqa: E402
from benchmark_report import compare_results, load_baseline  # noqa: E402
from release_metadata import extract_release_body  # noqa: E402


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


class BenchmarkTests(TestCase):
    def test_contract_is_normalized(self) -> None:
        values = parse_results([{"name": "sort", "value": 123, "unit": "ns/iter"}])
        self.assertEqual(values, [{"name": "sort", "value": 123.0, "unit": "ns/iter"}])

    def test_contract_rejects_empty_and_duplicate_names(self) -> None:
        with self.assertRaises(ValueError):
            parse_results([{"name": "", "value": 1, "unit": "ns/iter"}])
        with self.assertRaises(ValueError):
            parse_results(
                [
                    {"name": "sort", "value": 1, "unit": "ns/iter"},
                    {"name": "sort", "value": 2, "unit": "ns/iter"},
                ]
            )

    def test_exactly_twenty_percent_is_regression(self) -> None:
        _, regressions = compare_results({"sort": 120.0}, {"sort": 100.0})
        self.assertEqual(len(regressions), 1)

    def test_under_twenty_percent_and_new_benchmark_pass(self) -> None:
        rows, regressions = compare_results(
            {"sort": 119.99, "new": 10.0}, {"sort": 100.0}
        )
        self.assertEqual(regressions, [])
        self.assertEqual([row["status"] for row in rows], ["new", "ok"])

    @patch("benchmark_report.api", return_value=None)
    def test_missing_baseline_is_allowed(self, _api) -> None:
        self.assertIsNone(load_baseline("but212/rustica"))

    @patch.dict(os.environ, {"GH_TOKEN": "test-token"})
    @patch("benchmark_common.urlopen")
    def test_get_404_can_be_missing(self, urlopen) -> None:
        urlopen.side_effect = HTTPError(
            "https://api.github.com/missing", 404, "missing", {}, io.BytesIO(b"missing")
        )
        self.assertIsNone(api("GET", "/missing", allow_not_found=True))

    @patch.dict(os.environ, {"GH_TOKEN": "test-token"})
    @patch("benchmark_common.urlopen")
    def test_write_404_is_an_error(self, urlopen) -> None:
        for method in ("POST", "PUT"):
            with self.subTest(method=method):
                urlopen.side_effect = HTTPError(
                    "https://api.github.com/missing", 404, "missing", {}, io.BytesIO(b"missing")
                )
                with self.assertRaises(RuntimeError):
                    api(method, "/missing", {})

    def test_not_found_flag_is_get_only(self) -> None:
        with self.assertRaises(ValueError):
            api("POST", "/missing", {}, allow_not_found=True)


if __name__ == "__main__":
    main()
