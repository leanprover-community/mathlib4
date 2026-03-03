#!/usr/bin/env python3
"""
Update the public gist of frequent defeq_abuse failure patterns.

Reads from defeq_abuse_results.db, merges reversed pairs (A =?= B and B =?= A),
and pushes one .txt file per pattern (>= 10 occurrences) plus an index to GitHub.

Usage:
    python3 scripts/update_defeq_abuse_gist.py
"""

import json
import sqlite3
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

GIST_ID = "6a26f33c00bf444502eddf05296ec644"
GIST_URL = f"https://gist.github.com/kim-em/{GIST_ID}"
DB_PATH = Path(__file__).parent / "defeq_abuse_results.db"
MIN_OCCURRENCES = 10


def main():
    if not DB_PATH.exists():
        print(f"Database not found: {DB_PATH}", file=sys.stderr)
        sys.exit(1)

    conn = sqlite3.connect(str(DB_PATH))

    # Build canonical key for each failure (merge reversed pairs)
    canonical = {}
    for (f,) in conn.execute("SELECT DISTINCT failure FROM failures"):
        if " =?= " in f:
            lhs, rhs = f.split(" =?= ", 1)
            canonical[f] = " =?= ".join(sorted([lhs.strip(), rhs.strip()]))
        else:
            canonical[f] = f

    # Group by canonical key -> set of occurrence ids
    key_occs: dict[str, set[int]] = defaultdict(set)
    for failure, occ_id in conn.execute(
        "SELECT failure, occurrence_id FROM failures"
    ):
        key_occs[canonical[failure]].add(occ_id)

    # Filter and sort
    big_keys = [
        (k, len(v)) for k, v in key_occs.items() if len(v) >= MIN_OCCURRENCES
    ]
    big_keys.sort(key=lambda x: -x[1])
    print(f"{len(big_keys)} canonical patterns with >= {MIN_OCCURRENCES} occurrences")

    # Fetch all occurrence details
    occ_map = {}
    for row in conn.execute("SELECT id, file, line, decl_header FROM occurrences"):
        occ_map[row[0]] = (row[1], row[2], row[3])

    # Get list of existing files in the gist so we can delete stale ones
    result = subprocess.run(
        ["gh", "api", f"gists/{GIST_ID}", "--jq", ".files | keys[]"],
        capture_output=True, text=True, check=True,
    )
    existing_files = set(result.stdout.strip().split("\n"))

    # Build payload
    payload: dict = {"files": {}}

    # Delete all existing failure_*.txt files
    for name in existing_files:
        if name.startswith("failure_") and name.endswith(".txt"):
            payload["files"][name] = None

    # Build index and per-pattern files (1-indexed)
    idx = [
        "# defeq_abuse failure patterns",
        "",
        f"{len(big_keys)} canonical `=?=` patterns (reversed pairs merged), "
        f"each appearing in >= {MIN_OCCURRENCES} `set_option` occurrences.",
        "",
        "| # | pattern | occurrences | locations |",
        "|--:|--------|------------:|-----------|",
    ]

    for i, (key, cnt) in enumerate(big_keys, start=1):
        fname = f"failure_{i:03d}.txt"

        locs = sorted(
            [occ_map[oid] for oid in key_occs[key] if oid in occ_map]
        )
        lines = [f"# {key}", f"# {cnt} occurrences", ""]
        for file, line, decl in locs:
            decl_short = (decl or "").split("\n")[0][:150]
            lines.append(f"{file}:{line}  {decl_short}")

        payload["files"][fname] = {"content": "\n".join(lines) + "\n"}

        safe = key.replace("|", "\\|")
        anchor = f"file-{fname.replace('.', '-')}"
        idx.append(
            f"| {i} | `{safe}` | {cnt} | [locations]({GIST_URL}#{anchor}) |"
        )

    payload["files"]["00_index.md"] = {"content": "\n".join(idx) + "\n"}
    conn.close()

    # Push to GitHub
    payload_path = Path("/tmp/defeq_gist_payload.json")
    payload_path.write_text(json.dumps(payload))

    new_files = sum(1 for v in payload["files"].values() if v is not None)
    deletions = sum(1 for v in payload["files"].values() if v is None)
    print(f"Uploading {new_files} files, deleting {deletions} stale files...")

    subprocess.run(
        [
            "gh", "api", f"gists/{GIST_ID}",
            "-X", "PATCH",
            "--input", str(payload_path),
            "--jq", ".html_url",
        ],
        check=True,
    )


if __name__ == "__main__":
    main()
