#!/usr/bin/env python3
# sum up times of lines a la `elaboration 100ms`

import collections
import re
import sys

cats = collections.defaultdict(lambda: 0)
for line in sys.stdin:
    sys.stderr.write(line)
    if m := re.match("(.+?) ([\d.]+)(m?)s$", line):
        cats[m[1].strip()] += float(m[2]) * (1e-3 if m[3] else 1)

for cat in sorted(cats.keys()):
    cat2 = cat
    if len(sys.argv) > 1:
        cat2 = f"{sys.argv[1]} {cat}"
    # default unit to `s`
    if "|" not in cat2:
        cat2 += "|s"
    print(f"{cat2!r}: {cats[cat]:f}")
