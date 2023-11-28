#!/usr/bin/env python3

import pytz
import datetime
import github
import os
import re
import requests
import subprocess
import sys
import yaml
import networkx as nx
from collections import defaultdict
from pathlib import Path

# Must run from root of mathlib4 directory.

if not os.path.exists('port-repos/mathlib'):
    print("Make sure you are in the root of the mathlib4 directory")
    print("and have checked out mathlib under port-repos/mathlib.")
    sys.exit(1)

GITHUB_TOKEN_FILE = 'port-repos/github-token'
github_token = open(GITHUB_TOKEN_FILE).read().strip()

mathlib3_root = 'port-repos/mathlib'
mathlib4_root = './'

source_module_re = re.compile(r"^! .*source module (.*)$")
commit_re = re.compile(r"^! (leanprover-community/[a-z]*) commit ([0-9a-f]*)")
import_re = re.compile(r"^import ([^ ]*)")

align_import_re = re.compile(
    r'^#align_import ([^ ]*) from "(leanprover-community/[a-z]*)" ?@ ?"([0-9a-f]*)"')

def mk_label(path: Path) -> str:
    rel = path.relative_to(Path(mathlib3_root))
    rel = Path(*rel.parts[1:])
    return str(rel.with_suffix('')).replace(os.sep, '.')

paths = []
for path in Path(mathlib3_root).glob('**/*.lean'):
    if path.relative_to(mathlib3_root).parts[0] not in ['src', 'archive', 'counterexamples']:
        continue
    if path.relative_to(mathlib3_root).parts[1] in ['tactic', 'meta']:
        continue
    paths.append(path)

graph = nx.DiGraph()
for path in paths:
    graph.add_node(mk_label(path))

for path in paths:
    label = mk_label(path)
    for line in path.read_text().split('\n'):
        m = import_re.match(line)
        if m:
            imported = m.group(1)
            if imported.startswith('tactic.') or imported.startswith('meta.') or imported.startswith('.'):
                continue
            if imported not in graph.nodes:
                if imported + '.default' in graph.nodes:
                    imported = imported + '.default'
                else:
                    imported = imported
            graph.add_edge(imported, label)

def get_mathlib4_module_commit_info(contents):
    module = repo = commit = None
    for line in contents.split('\n'):
        m = align_import_re.match(line)
        if m:
            module = m.group(1)
            repo = m.group(2)
            commit = m.group(3)
            break
        m = source_module_re.match(line)
        if m:
            module = m.group(1)
        m = commit_re.match(line)
        if m:
            repo = m.group(1)
            commit = m.group(2)
    return module, repo, commit

# contains ported files
# lean 3 module name -> { mathlib4_file, mathlib3_hash }
data = dict()
for path4 in Path(mathlib4_root).glob('**/*.lean'):
    # we definitely do not want to look in `port-repos` here!
    if path4.relative_to(mathlib4_root).parts[0] not in ('Mathlib', 'Archive', 'Counterexamples'):
        continue
    module, repo, commit = get_mathlib4_module_commit_info(path4.read_text())
    if module is None:
        continue

    if commit is None:
        print(f"Commit is None for module: {module}")
        continue

    log = subprocess.run(
        ['git', 'log', '--oneline', str(path4)],
        capture_output=True)
    pr_matches = re.search(r'#([0-9]+)\)$', log.stdout.decode().splitlines()[-1])
    if pr_matches:
        mathlib4_pr = int(pr_matches.groups()[0])
    else:
        mathlib4_pr = None

    data[module] = {
        'mathlib4_file': str(path4.relative_to(mathlib4_root)),
        'mathlib4_pr': mathlib4_pr,
        'source': dict(repo=repo, commit=commit)
    }

    graph.add_node(module)

prs = {}
fetch_args = ['git', 'fetch', 'origin']
nums = []
sync_prs = defaultdict(set)
mathlib4repo = github.Github(github_token).get_repo("leanprover-community/mathlib4")
for pr in mathlib4repo.get_pulls(state='open'):
    if pr.created_at < datetime.datetime(2022, 12, 1, 0, 0, 0, tzinfo=pytz.UTC):
        continue
    if 'no-source-header' in (l.name for l in pr.labels):
        continue
    if 'mathlib3-pair' in (l.name for l in pr.labels):
        for file in (f.filename for f in pr.get_files()):
            sync_prs[file].add(pr.number)
    num = pr.number
    nums.append(num)
    prs[num] = pr
    fetch_args.append(f'pull/{num}/head:port-status-pull/{num}')

os.system("git branch -D $(git branch --list 'port-status-pull/*')")
subprocess.run(fetch_args)

prs_of_import = {}
for num in nums:
    p = subprocess.run(
        ['git', 'diff', '--name-only', '--diff-filter=A',
         f'origin/master...port-status-pull/{num}'],
        capture_output=True)
    for l in p.stdout.decode().splitlines():
        f = subprocess.run(
            ['git', 'cat-file', 'blob', f'port-status-pull/{num}:{l}'],
            capture_output=True)
        import_, repo, commit = get_mathlib4_module_commit_info(f.stdout.decode(encoding='utf8', errors='replace'))
        prs_of_import.setdefault(import_, []).append({'pr': num, 'repo': repo, 'commit': commit, 'fname': l})

COMMENTS_URL = "https://raw.githubusercontent.com/wiki/leanprover-community/mathlib4/port-comments.md"
comments_dict = yaml.safe_load(requests.get(COMMENTS_URL).content.replace(b"```", b""))

yaml_dict = {}
new_yaml_dict = {}
for node in sorted(graph.nodes):
    if node in data:
        new_status = dict(
            ported=True,
            mathlib4_file=data[node]['mathlib4_file'],
            mathlib4_pr=data[node]['mathlib4_pr'],
            source=data[node]['source']
        )
        _sync_prs = [
            dict(
                num=sync_pr_num,
                labels=[dict(name=l.name, color=l.color) for l in prs[sync_pr_num].labels]
            )
            for sync_pr_num in sync_prs[data[node]['mathlib4_file']]
        ]
        if _sync_prs:
            new_status.update(mathlib4_sync_prs=_sync_prs)
        pr_status = f"mathlib4#{data[node]['mathlib4_pr']}" if data[node]['mathlib4_pr'] is not None else "_"
        sha = data[node]['source']['commit'] if data[node]['source']['repo'] == 'leanprover-community/mathlib' else "_"

        status = f"Yes {pr_status} {sha}"
    else:
        new_status = dict(ported=False)
        status = f'No'
        if node in prs_of_import:
            pr_info = prs_of_import[node][0]
            if pr_info['commit'] is None:
                print('PR seems to be missing a source header', node, pr_info)
                assert(False)
            new_status.update(
                mathlib4_pr=pr_info['pr'],
                mathlib4_file=pr_info['fname'],
                source=dict(repo=pr_info['repo'], commit=pr_info['commit']))
            labels = [{'name': l.name, 'color': l.color} for l in prs[pr_info['pr']].labels]
            if labels:
                new_status.update(labels=labels)
            sha = pr_info['commit'] if pr_info['repo'] == 'leanprover-community/mathlib' else "_"
            status += f" mathlib4#{pr_info['pr']} {sha}"
    try:
        comment_data = comments_dict[node]
    except KeyError:
        pass
    else:
        if isinstance(comment_data, str):
            # old comment format
            comment_data = dict(message=comment_data)
        # new comment format
        status += ' ' + comment_data['message']
        new_status.update(comment=comment_data)
    yaml_dict[node] = status
    new_yaml_dict[node] = new_status

DO_NOT_EDIT_MESSAGE = """
# Do not edit this file.
# If you want to add free-form comments about files that don't have PRs yet,
# edit https://github.com/leanprover-community/mathlib4/wiki/port-comments/_edit instead.
""" + ("\n" * 37)

with open('port_status.yaml', 'w') as f:
    f.write(DO_NOT_EDIT_MESSAGE + "```\n" + yaml.dump(yaml_dict) + "```\n")
with open('port_status_new.yaml', 'w') as f:
    f.write(DO_NOT_EDIT_MESSAGE + "```\n" + yaml.dump(new_yaml_dict) + "```\n")
