from __future__ import annotations

import argparse
from dataclasses import dataclass
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


def parse_benchmark_output(text: str) -> list[BenchmarkEntry]:
    entries: list[BenchmarkEntry] = []
    for line in text.splitlines():
        line = line.strip()
        match = LINE_REGEX.match(line)
        if match:
            group, name, mean, median, p95, min_val, max_val, iters, throughput = match.groups()
            entries.append(
                BenchmarkEntry(
                    group=group,
                    name=name,
                    mean=mean,
                    min=min_val,
                    max=max_val,
                    iters=int(iters),
                    median=median if median else "-",
                    p95=p95 if p95 else "-",
                    throughput=throughput if throughput else "-",
                )
            )

    if not entries:
        raise ValueError("No benchmark results found in input text")
    return entries


def render_markdown_report(
    entries: list[BenchmarkEntry],
    title: str = "Benchmark Results",
    commit_hash: str | None = None,
) -> str:
    groups: dict[str, list[BenchmarkEntry]] = {}
    for entry in entries:
        groups.setdefault(entry.group, []).append(entry)

    now_utc = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    lines: list[str] = [f"# {title}", ""]

    meta_parts = [f"Generated on {now_utc}"]
    if commit_hash:
        meta_parts.append(f"Commit: `{commit_hash}`")
    lines.append(f"> {', '.join(meta_parts)}")
    lines.append("")

    for group_name, group_entries in groups.items():
        lines.append(f"## {group_name}")
        lines.append("")
        lines.append("| Benchmark | Mean | Median | P95 | Min | Max | Iterations | Throughput |")
        lines.append("| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |")
        for e in group_entries:
            lines.append(
                f"| `{e.name}` | {e.mean} | {e.median} | {e.p95} | {e.min} | {e.max} | {e.iters} | {e.throughput} |"
            )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def get_git_commit_hash(repo_dir: Path) -> str | None:
    try:
        res = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
        return res.stdout.strip()
    except Exception:
        return None


def run_cargo_bench(repo_dir: Path) -> str:
    cmd = ["cargo", "bench", "--bench", "datatypes_benchmarks", "--features", "pvec", "--locked"]
    print(f"Executing: {' '.join(cmd)}")
    res = subprocess.run(
        cmd,
        cwd=repo_dir,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return res.stdout


def resolve_input(repo_dir: Path, input_path: Path | None, force_run: bool) -> str:
    if force_run:
        return run_cargo_bench(repo_dir)

    if input_path:
        if not input_path.exists():
            raise FileNotFoundError(f"Specified input file does not exist: {input_path}")
        return input_path.read_text(encoding="utf-8")

    candidate_files = ["benchmark_raw.txt", "benchmark_result.txt"]
    for filename in candidate_files:
        candidate = repo_dir / filename
        if candidate.exists():
            print(f"Using existing benchmark artifact: {candidate}")
            return candidate.read_text(encoding="utf-8")

    print("No benchmark raw artifact found. Running cargo bench locally...")
    return run_cargo_bench(repo_dir)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate markdown benchmark report.")
    parser.add_argument(
        "--input",
        "-i",
        type=Path,
        default=None,
        help="Path to raw benchmark output file. If omitted, checks for benchmark_raw.txt or runs cargo bench.",
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

    args = parser.parse_args(argv)
    repo_root = Path(__file__).resolve().parent.parent.parent

    try:
        raw_text = resolve_input(repo_root, args.input, args.run)
        entries = parse_benchmark_output(raw_text)
        commit = get_git_commit_hash(repo_root)
        markdown = render_markdown_report(entries, commit_hash=commit)

        output_path = args.output
        if not output_path.is_absolute():
            output_path = repo_root / output_path

        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(markdown, encoding="utf-8")
        print(f"Successfully generated benchmark report at: {output_path} ({len(entries)} benchmarks)")
        return 0
    except Exception as err:
        print(f"Error: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
