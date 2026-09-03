from __future__ import annotations

import sys
from pathlib import Path
from unittest import TestCase, main


SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

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


if __name__ == "__main__":
    main()
