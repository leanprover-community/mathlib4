#!/usr/bin/env python3

import os
import re
import yaml
import networkx as nx
import subprocess
from pathlib import Path

mathlib3_root = 'port-repos/mathlib/src'
mathlib4_root = 'Mathlib/'

source_module_re = re.compile(r"^! .*source module (.*)$")
commit_re = re.compile(r"^! leanprover-community/mathlib commit ([0-9a-f]*)$")
import_re = re.compile(r"^import ([^ ]*)")
synchronized_re = re.compile(r".*SYNCHRONIZED WITH MATHLIB4.*")

# Not using re.compile as this is passed to git which uses a different regex dialect:
# https://www.sjoerdlangkemper.nl/2021/08/13/how-does-git-diff-ignore-matching-lines-work/
comment_git_re = r'\`(' + r'|'.join([
    re.escape("> THIS FILE IS SYNCHRONIZED WITH MATHLIB4."),
    re.escape("> https://github.com/leanprover-community/mathlib4/pull/") + r"[0-9]*",
    re.escape("> Any changes to this file require a corresponding PR to mathlib4."),
    r"",
]) + r")" + "\n"

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path(mathlib3_root))
    return str(rel.with_suffix('')).replace(os.sep, '.')

# TODO: Make sure port-repos/ repos exist & are up-to-date.

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

# contains ported files
# lean 3 module name -> { mathlib4_file, mathlib3_hash }
data = dict()
for path4 in Path(mathlib4_root).glob('**/*.lean'):
    if path4.relative_to(mathlib4_root).parts[0] in \
       ['Init', 'Lean', 'Mathport', 'Tactic', 'Testing', 'Util']:
        continue
    module = None
    commit = None
    for line in path4.read_text().split('\n'):
        m = source_module_re.match(line)
        if m:
            module = m.group(1)
        m = commit_re.match(line)
        if m:
            commit = m.group(1)
        if import_re.match(line):
            break
    if module is None:
        continue

    assert commit is not None
    data[module] = {
        'mathlib4_file': path4.relative_to(mathlib4_root),
        'mathlib3_hash': commit
    }

allDone = dict()
parentsDone = dict()
verified = dict()
touched = dict()
for node in graph.nodes:
    if node in data:
        git_command = ['git', 'diff', '--quiet',
            # f'--ignore-matching-lines={comment_git_re}',
            data[node]['mathlib3_hash'] + "..HEAD", "--", "src" + os.sep + node.replace('.', os.sep) + ".lean"]
        result = subprocess.run(git_command, cwd='port-repos/mathlib')
        if result.returncode == 1:
            git_command.remove('--quiet')
            # git_command.remove(f'--ignore-matching-lines={comment_git_re}')
            touched[node] = git_command
    ancestors = nx.ancestors(graph, node)
    if all(imported in data for imported in ancestors) and not node in data:
        allDone[node] = (len(nx.descendants(graph, node)), "")
    else:
        if all(imported in data for imported in graph.predecessors(node)) and not node in data:
            parentsDone[node] = (len(nx.descendants(graph, node)), "")

print('# The following files have all dependencies ported already, and should be ready to port:')
print('# Earlier items in the list are required in more places in mathlib.')
allDone = dict(sorted(allDone.items(), key=lambda item: -item[1][0]))
for k, v in allDone.items():
    if v[1] == "":
        print(k)
    else:
        print(k + "    -- " + v[1])

