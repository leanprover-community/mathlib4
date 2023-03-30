#!/usr/bin/env python3
import sys
from collections import deque

lns = deque([], 2)
with open(sys.argv[1], "r", encoding="utf-8", newline="\n") as f, \
      open(sys.argv[2], "w", encoding="utf-8", newline="\n") as g:
    for ln_raw in f:
        ln = ln_raw.strip("\n")
        lns.append(ln)
        if len(lns) <= 1:
            continue
        if lns[1].lstrip() == "by" and len(lns[0]) < 98 and not lns[0].lstrip().startswith("--"):
            lns.pop()
            lns[0] += " by"
        elif lns[1].lstrip() == "where" and len(lns[0]) < 95 and not lns[0].lstrip().startswith("--"):
            lns.pop()
            lns[0] += " where"
        else:
            print(lns[0], file=g)
    lns.popleft()
    for ln in lns:
        print(ln, file=g)
