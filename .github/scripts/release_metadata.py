"""Extract a release section from CHANGELOG.md."""

from __future__ import annotations

import re
import sys
from pathlib import Path


def extract_release_body(version: str, changelog: str) -> str:
    lines = changelog.splitlines()
    heading = re.compile(
        rf"^## \[{re.escape(version)}\](?:\s+-\s+\d{{4}}-\d{{2}}-\d{{2}})?\s*$"
    )
    start = next((index for index, line in enumerate(lines) if heading.match(line)), None)
    if start is None:
        raise ValueError(f"No exact CHANGELOG entry found for {version}")

    end = next(
        (index for index in range(start + 1, len(lines)) if lines[index].startswith("## ")),
        len(lines),
    )
    body = "\n".join(lines[start + 1 : end]).strip()
    if not body:
        raise ValueError(f"CHANGELOG entry for {version} is empty")
    return body


def main() -> int:
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: release_metadata.py VERSION [CHANGELOG]")

    version = sys.argv[1]
    changelog_path = Path(sys.argv[2]) if len(sys.argv) == 3 else Path("CHANGELOG.md")
    body = extract_release_body(version, changelog_path.read_text(encoding="utf-8"))
    print(body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
