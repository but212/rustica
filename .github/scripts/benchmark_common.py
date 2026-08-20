"""Shared validation and GitHub API helpers for benchmark workflows."""

from __future__ import annotations

import json
import math
import os
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen


API_ROOT = "https://api.github.com"


def api(method: str, path: str, payload: dict | None = None, allow_not_found: bool = False):
    if allow_not_found and method != "GET":
        raise ValueError("allow_not_found is only valid for GET requests")

    token = os.environ["GH_TOKEN"]
    body = None if payload is None else json.dumps(payload).encode("utf-8")
    request = Request(
        API_ROOT + path,
        data=body,
        method=method,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
            "Content-Type": "application/json",
        },
    )
    try:
        with urlopen(request, timeout=30) as response:
            raw = response.read()
            return json.loads(raw) if raw else None
    except HTTPError as error:
        if allow_not_found and error.code == 404:
            return None
        detail = error.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"GitHub API {method} {path} failed ({error.code}): {detail}") from error


def parse_results(values: object) -> list[dict]:
    if not isinstance(values, list) or not values:
        raise ValueError("benchmark result must be a non-empty JSON array")

    results: list[dict] = []
    names: set[str] = set()
    for item in values:
        if not isinstance(item, dict):
            raise ValueError("benchmark result contains an invalid entry")
        name = item.get("name")
        value = item.get("value")
        if (
            not isinstance(name, str)
            or not name.strip()
            or isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value <= 0
            or item.get("unit") != "ns/iter"
            or name in names
        ):
            raise ValueError("benchmark result contains an invalid entry")
        names.add(name)
        results.append({"name": name, "value": float(value), "unit": "ns/iter"})
    return results


def read_results(path: Path) -> list[dict]:
    return parse_results(json.loads(path.read_text(encoding="utf-8")))
