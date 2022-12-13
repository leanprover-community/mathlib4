#!/usr/bin/env python3

import os
import re
import yaml
import networkx as nx
import subprocess
from pathlib import Path

mathlib3_root = 'port-repos/mathlib/src'

import_re = re.compile(r"^import ([^ ]*)")
synchronized_re = re.compile(r".*SYNCHRONIZED WITH MATHLIB4.*")

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path(mathlib3_root))
    return str(rel.with_suffix('')).replace(os.sep, '.')

graph = nx.DiGraph()

for path in Path(mathlib3_root).glob('**/*.lean'):
    if path.relative_to(mathlib3_root).parts[0] in ['tactic', 'meta']:
        continue
    graph.add_node(mk_label(path))

synchronized = dict()

for path in Path(mathlib3_root).glob('**/*.lean'):
    if path.relative_to(mathlib3_root).parts[0] in ['tactic', 'meta']:
        continue
    label = mk_label(path)
    for line in path.read_text().split('\n'):
        m = import_re.match(line)
        if m:
            imported = m.group(1)
            if imported.startswith('tactic.') or imported.startswith('meta.'):
                continue
            if imported not in graph.nodes:
                if imported + '.default' in graph.nodes:
                    imported = imported + '.default'
                else:
                    imported = 'lean_core.' + imported
            graph.add_edge(imported, label)
        if synchronized_re.match(line):
            synchronized[label] = True

for node in sorted(graph.nodes):
    print(node)
