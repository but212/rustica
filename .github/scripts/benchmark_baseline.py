"""Store the latest trusted main benchmark result on the gh-pages branch."""

from __future__ import annotations

import base64
import json
import os
import sys
from pathlib import Path

from benchmark_common import api, read_results


BRANCH = "gh-pages"
BASELINE_PATH = "benchmarks/rustica.json"


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: benchmark_baseline.py FORMATTED_RESULTS.json")

    results_path = Path(sys.argv[1])
    results = read_results(results_path)
    repository = os.environ["GITHUB_REPOSITORY"]
    encoded = base64.b64encode((json.dumps(results, indent=2) + "\n").encode("utf-8")).decode("ascii")

    ref_path = f"/repos/{repository}/git/ref/heads/{BRANCH}"
    if api("GET", ref_path, allow_not_found=True) is None:
        api("POST", f"/repos/{repository}/git/refs", {"ref": f"refs/heads/{BRANCH}", "sha": os.environ["GITHUB_SHA"]})

    content_path = f"/repos/{repository}/contents/{BASELINE_PATH}?ref={BRANCH}"
    current = api("GET", content_path, allow_not_found=True)
    payload = {
        "message": "ci: update benchmark baseline",
        "content": encoded,
        "branch": BRANCH,
    }
    if current is not None:
        payload["sha"] = current["sha"]
    api("PUT", f"/repos/{repository}/contents/{BASELINE_PATH}", payload)
    print(f"Updated {BRANCH}/{BASELINE_PATH} with {len(results)} benchmark(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
