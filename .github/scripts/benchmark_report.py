from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
import re
import subprocess
import sys


LINE_REGEX = re.compile(
    r"^([A-Za-z0-9_]+)/([^\s]+)\s+\.\.\.\s+mean:\s*([^\s]+)(?:\s+median:\s*([^\s]+)\s+p95:\s*([^\s]+))?\s+min:\s*([^\s]+)\s+max:\s*([^\s]+)\s+\((\d+)\s+iters\)(?:\s+\[(.*?)\])?$"
)


@dataclass(frozen=True)
class BenchmarkEntry:
    group: str
    name: str
    mean: str
    min: str
    max: str
    iters: int
    median: str = "-"
    p95: str = "-"
    throughput: str = "-"

    @classmethod
    def from_line(cls, line: str) -> BenchmarkEntry | None:
        match = LINE_REGEX.match(line.strip())
        if not match:
            return None
        group, name, mean, median, p95, min_val, max_val, iters, throughput = match.groups()
        return cls(
            group=group,
            name=name,
            mean=mean,
            median=median or "-",
            p95=p95 or "-",
            min=min_val,
            max=max_val,
            iters=int(iters),
            throughput=throughput or "-",
        )

    def to_markdown_row(self) -> str:
        return (
            f"| `{self.name}` | {self.mean} | {self.median} | {self.p95} | "
            f"{self.min} | {self.max} | {self.iters} | {self.throughput} |"
        )


@dataclass
class BenchmarkReport:
    entries: list[BenchmarkEntry]
    title: str = "Benchmark Results"
    commit_hash: str | None = None
    generated_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))

    def __post_init__(self) -> None:
        if not self.entries:
            raise ValueError("No benchmark results found in input text")

    @classmethod
    def from_raw_text(
        cls,
        text: str,
        title: str = "Benchmark Results",
        commit_hash: str | None = None,
    ) -> BenchmarkReport:
        parsed = [
            entry
            for line in text.splitlines()
            if (entry := BenchmarkEntry.from_line(line)) is not None
        ]
        return cls(entries=parsed, title=title, commit_hash=commit_hash)

    def _grouped_entries(self) -> dict[str, list[BenchmarkEntry]]:
        groups: dict[str, list[BenchmarkEntry]] = {}
        for entry in self.entries:
            groups.setdefault(entry.group, []).append(entry)
        return groups

    def to_markdown(self) -> str:
        now_utc = self.generated_at.strftime("%Y-%m-%d %H:%M:%S UTC")
        meta = [f"Generated on {now_utc}"]
        if self.commit_hash:
            meta.append(f"Commit: `{self.commit_hash}`")

        lines: list[str] = [
            f"# {self.title}",
            "",
            f"> {', '.join(meta)}",
            "",
        ]

        for group_name, entries in self._grouped_entries().items():
            lines.extend([
                f"## {group_name}",
                "",
                "| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |",
                "| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |",
                *(entry.to_markdown_row() for entry in entries),
                "",
            ])

        return "\n".join(lines).rstrip() + "\n"

    def write_to(self, output_path: Path) -> None:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(self.to_markdown(), encoding="utf-8")


@dataclass(frozen=True)
class BenchmarkRunner:
    repo_dir: Path
    candidate_files: tuple[str, ...] = ("benchmark_raw.txt", "benchmark_result.txt")

    def get_commit_hash(self) -> str | None:
        try:
            res = subprocess.run(
                ["git", "rev-parse", "--short", "HEAD"],
                cwd=self.repo_dir,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                check=True,
            )
            return res.stdout.strip()
        except Exception:
            return None

    def execute_cargo_bench(self) -> str:
        cmd = ["cargo", "bench", "--bench", "datatypes_benchmarks", "--features", "pvec", "--locked"]
        print(f"Executing: {' '.join(cmd)}")
        res = subprocess.run(
            cmd,
            cwd=self.repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
        return res.stdout

    def resolve_raw_output(self, input_path: Path | None, force_run: bool) -> str:
        if force_run:
            return self.execute_cargo_bench()

        if input_path:
            if not input_path.exists():
                raise FileNotFoundError(f"Specified input file does not exist: {input_path}")
            return input_path.read_text(encoding="utf-8")

        for filename in self.candidate_files:
            candidate = self.repo_dir / filename
            if candidate.exists():
                print(f"Using existing benchmark artifact: {candidate}")
                return candidate.read_text(encoding="utf-8")

        print("No benchmark raw artifact found. Running cargo bench locally...")
        return self.execute_cargo_bench()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate markdown benchmark report.")
    parser.add_argument(
        "--input",
        "-i",
        type=Path,
        default=None,
        help="Path to raw benchmark output file. If omitted, checks artifacts or runs cargo bench.",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=Path,
        default=Path("docs/benchmark_result.md"),
        help="Path to markdown output file (default: docs/benchmark_result.md).",
    )
    parser.add_argument(
        "--run",
        action="store_true",
        help="Force running cargo bench locally instead of using an existing artifact.",
    )

    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")

    args = parser.parse_args(argv)
    repo_root = Path(__file__).resolve().parent.parent.parent

    try:
        runner = BenchmarkRunner(repo_root)
        raw_text = runner.resolve_raw_output(args.input, args.run)

        report = BenchmarkReport.from_raw_text(
            text=raw_text,
            commit_hash=runner.get_commit_hash(),
        )

        output_path = args.output if args.output.is_absolute() else repo_root / args.output
        report.write_to(output_path)

        print(f"Successfully generated benchmark report at: {output_path} ({len(report.entries)} benchmarks)")
        return 0
    except Exception as err:
        print(f"Error: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())