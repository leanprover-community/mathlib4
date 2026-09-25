#!/usr/bin/env python3
"""Convert runLinter `--trace` completion lines into per-linter radar measurements.

Input lines look like
  [Mathlib] - simpNF: (2/2) Passed! [582144 decls, summed task time 13350949 ms, 6509814279 heartbeats]
Linters run concurrently, so these per-task sums (not wall-clock gaps between trace lines)
are the meaningful per-linter cost. Heartbeats are deterministic and hardware-independent.
"""
import json
import re
import sys

LINE = re.compile(
    r"- (?P<linter>\w+): \(2/2\) .*\[(?P<decls>\d+) decls, summed task time (?P<ms>\d+) ms, "
    r"(?P<hb>\d+) heartbeats\]"
)

for line in open(sys.argv[1], errors="replace"):
    if m := LINE.search(line):
        topic = f"lint/linter/{m['linter']}"
        print(json.dumps({"metric": f"{topic}//heartbeats", "value": int(m["hb"])}))
        print(json.dumps({"metric": f"{topic}//task-time", "value": int(m["ms"]) / 1000, "unit": "s"}))
        print(json.dumps({"metric": f"{topic}//decls", "value": int(m["decls"])}))
