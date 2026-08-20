"""Compare a PR benchmark artifact with the trusted gh-pages baseline."""

from __future__ import annotations

import base64
import json
import os
import sys
from html import escape
from pathlib import Path

from benchmark_common import api, parse_results, read_results, results_by_name


BASELINE_PATH = "benchmarks/rustica.json"
THRESHOLD = 1.20
MARKER = "<!-- rustica-benchmark-regression -->"


def find_candidate(directory: Path) -> Path:
    direct = directory / "formatted_benchmark_results.json"
    if direct.is_file():
        return direct
    matches = list(directory.rglob("formatted_benchmark_results.json"))
    if len(matches) != 1:
        raise FileNotFoundError("could not identify exactly one benchmark result file")
    return matches[0]


def load_baseline(repository: str) -> dict[str, float] | None:
    path = f"/repos/{repository}/contents/{BASELINE_PATH}?ref=gh-pages"
    response = api("GET", path, allow_not_found=True)
    if response is None:
        return None
    content = base64.b64decode(response["content"]).decode("utf-8")
    return results_by_name(parse_results(json.loads(content)))


def markdown_table(rows: list[dict]) -> str:
    lines = [
        "| Benchmark | Baseline (ns/iter) | Candidate (ns/iter) | Change | Result |",
        "|---|---:|---:|---:|---|",
    ]
    for row in rows:
        name = escape(row["name"].replace("|", "\\|"))
        if row["status"] == "new":
            lines.append(f"| {name} | — | {row['candidate']:.2f} | new | not compared |")
        else:
            lines.append(
                f"| {name} | {row['baseline']:.2f} | {row['candidate']:.2f} | "
                f"{row['change']:+.2%} | {row['status']} |"
            )
    return "\n".join(lines)


def compare_results(candidate: dict[str, float], baseline: dict[str, float]) -> tuple[list[dict], list[str]]:
    rows: list[dict] = []
    regressions: list[str] = []
    for name, candidate_value in sorted(candidate.items()):
        if name not in baseline:
            rows.append({"name": name, "candidate": candidate_value, "status": "new"})
            continue
        baseline_value = baseline[name]
        change = candidate_value / baseline_value - 1.0
        status = "regression" if candidate_value >= baseline_value * THRESHOLD else "ok"
        rows.append(
            {
                "name": name,
                "baseline": baseline_value,
                "candidate": candidate_value,
                "change": change,
                "status": status,
            }
        )
        if status == "regression":
            regressions.append(f"{name} ({change:+.2%})")
    return rows, regressions


def publish_report(repository: str, pr_number: int, head_sha: str, conclusion: str, summary: str, run_id: int) -> None:
    check = {
        "name": "Benchmark regression",
        "head_sha": head_sha,
        "status": "completed",
        "conclusion": conclusion,
        "details_url": f"https://github.com/{repository}/actions/runs/{run_id}",
        "output": {
            "title": "Benchmark regression check",
            "summary": summary,
        },
    }
    api("POST", f"/repos/{repository}/check-runs", check)

    comments = api("GET", f"/repos/{repository}/issues/{pr_number}/comments?per_page=100") or []
    body = f"{MARKER}\n## Benchmark regression\n\n{summary}"
    existing = next((comment for comment in comments if MARKER in comment.get("body", "")), None)
    if existing:
        api("PATCH", f"/repos/{repository}/issues/comments/{existing['id']}", {"body": body})
    else:
        api("POST", f"/repos/{repository}/issues/{pr_number}/comments", {"body": body})


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: benchmark_report.py ARTIFACT_DIRECTORY")

    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
    workflow_run = event["workflow_run"]
    pull_requests = workflow_run.get("pull_requests", [])
    if workflow_run.get("event") != "pull_request" or not pull_requests:
        print("No pull request benchmark run to report")
        return 0

    repository = os.environ["GITHUB_REPOSITORY"]
    pr_number = int(pull_requests[0]["number"])
    head_sha = workflow_run["head_sha"]
    run_id = int(workflow_run["id"])
    candidate = results_by_name(read_results(find_candidate(Path(sys.argv[1]))))
    baseline = load_baseline(repository)

    if baseline is None:
        summary = "No `gh-pages/benchmarks/rustica.json` baseline exists yet; this result is informational."
        publish_report(repository, pr_number, head_sha, "neutral", summary, run_id)
        return 0

    rows, regressions = compare_results(candidate, baseline)

    table = markdown_table(rows)
    if regressions:
        summary = f"**Failed:** benchmark(s) are at least 20% slower: {', '.join(regressions)}.\n\n{table}"
        conclusion = "failure"
    else:
        summary = f"**Passed:** no benchmark is at least 20% slower than the baseline.\n\n{table}"
        conclusion = "success"

    publish_report(repository, pr_number, head_sha, conclusion, summary, run_id)
    print(summary)
    return 1 if regressions else 0


if __name__ == "__main__":
    raise SystemExit(main())
