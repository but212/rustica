"""Extract a release section from CHANGELOG.md."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys


SECTION_HEADING_REGEX = re.compile(
    r"^##\s+\[(?P<version>[^\]]+)\](?:\s+-\s+(?P<date>\d{4}-\d{2}-\d{2}))?\s*$"
)


@dataclass(frozen=True)
class ReleaseEntry:
    version: str
    body: str
    date: str | None = None

    def __post_init__(self) -> None:
        if not self.body:
            raise ValueError(f"CHANGELOG entry for {self.version} is empty")

    def ensure_non_empty(self) -> None:
        if not self.body:
            raise ValueError(f"CHANGELOG entry for {self.version} is empty")


@dataclass(frozen=True)
class Changelog:
    _raw_entries: dict[str, tuple[str | None, str]]

    @property
    def entries(self) -> dict[str, ReleaseEntry]:
        return {
            version: ReleaseEntry(version=version, date=date, body=body)
            for version, (date, body) in self._raw_entries.items()
            if body
        }

    @classmethod
    def from_markdown(cls, markdown: str) -> Changelog:
        raw_entries: dict[str, tuple[str | None, str]] = {}
        current_version: str | None = None
        current_date: str | None = None
        current_lines: list[str] = []

        for line in markdown.splitlines():
            if line.startswith("## "):
                if current_version is not None:
                    body = "\n".join(current_lines).strip()
                    if current_version not in raw_entries:
                        raw_entries[current_version] = (current_date, body)
                    current_lines.clear()

                match = SECTION_HEADING_REGEX.match(line)
                if match:
                    current_version = match.group("version")
                    current_date = match.group("date")
                else:
                    current_version = None
                    current_date = None
            elif current_version is not None:
                current_lines.append(line)

        if current_version is not None:
            body = "\n".join(current_lines).strip()
            if current_version not in raw_entries:
                raw_entries[current_version] = (current_date, body)

        return cls(_raw_entries=raw_entries)

    def get_entry(self, version: str) -> ReleaseEntry:
        if version not in self._raw_entries:
            raise ValueError(f"No exact CHANGELOG entry found for {version}")
        date, body = self._raw_entries[version]
        return ReleaseEntry(version=version, date=date, body=body)

    def extract_body(self, version: str) -> str:
        return self.get_entry(version).body


def extract_release_body(version: str, changelog: str) -> str:
    return Changelog.from_markdown(changelog).extract_body(version)


def main() -> int:
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: release_metadata.py VERSION [CHANGELOG]")

    version = sys.argv[1]
    changelog_path = Path(sys.argv[2]) if len(sys.argv) == 3 else Path("CHANGELOG.md")

    if not changelog_path.exists():
        raise FileNotFoundError(f"Changelog file not found: {changelog_path}")

    changelog = Changelog.from_markdown(changelog_path.read_text(encoding="utf-8"))
    body = changelog.extract_body(version)

    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
