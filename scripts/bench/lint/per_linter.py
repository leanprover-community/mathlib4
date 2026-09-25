#!/usr/bin/env python3
"""Convert runLinter `--trace` completion lines into per-linter radar measurements.

Input lines look like
  [Mathlib] - simpNF: (2/2) Passed! [582144 decls, summed task time 13350949 ms, 6518883316 heartbeats]
Linters run concurrently, so these per-task sums (not wall-clock gaps between trace lines)
are the meaningful per-linter cost. Heartbeats are deterministic and hardware-independent.

Exits nonzero, recording nothing, unless the log has at least one cost line and the
`Completed linting!` trace: a crashed run or a changed trace format must not silently
produce no or partial per-linter data.
"""
import json
import re
import sys

LINE = re.compile(
    r"\] - (?P<linter>.+?): \(2/2\) .*\[(?P<decls>\d+) decls, summed task time (?P<ms>\d+) ms, "
    r"(?P<hb>\d+) heartbeats\]$"
)

text = open(sys.argv[1], errors="replace").read()
records = {}
for line in text.splitlines():
    if m := LINE.search(line):
        if m["linter"] in records:
            sys.exit(f"per_linter.py: {m['linter']} reported twice")
        records[m["linter"]] = m
if not records or "Completed linting!" not in text:
    sys.exit("per_linter.py: no complete per-linter cost report in the runLinter trace")
for name, m in records.items():
    topic = f"lint/linter/{name}"
    print(json.dumps({"metric": f"{topic}//heartbeats", "value": int(m["hb"])}))
    print(json.dumps({"metric": f"{topic}//task-time", "value": int(m["ms"]) / 1000, "unit": "s"}))
    print(json.dumps({"metric": f"{topic}//decls", "value": int(m["decls"])}))
