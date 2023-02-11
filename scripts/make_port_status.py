#!/usr/bin/env python3

import datetime
import github
import os
import re
import requests
import subprocess
import sys
import yaml
import networkx as nx
from pathlib import Path

# Must run from root of mathlib4 directory.

if not os.path.exists('port-repos/mathlib'):
    print("Make sure you are in the root of the mathlib4 directory")
    print("and have checked out mathlib under port-repos/mathlib.")
    sys.exit(1)

GITHUB_TOKEN_FILE = 'port-repos/github-token'
github_token = open(GITHUB_TOKEN_FILE).read().strip()

mathlib3_root = 'port-repos/mathlib/src'
mathlib4_root = 'Mathlib/'

source_module_re = re.compile(r"^! .*source module (.*)$")
commit_re = re.compile(r"^! (leanprover-community/[a-z]*) commit ([0-9a-f]*)")
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

def condense(s):
    if s.startswith('Mathlib/'):
        s = s[len('Mathlib/'):]
    if s.endswith('.lean'):
        s = s[:-5]
    s = s.lower()
    s = s.replace('/', '.')
    s = s.replace('_', '')
    return s

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

def get_mathlib4_module_commit_info(contents):
    module = repo = commit = None
    for line in contents.split('\n'):
        m = source_module_re.match(line)
        if m:
            module = m.group(1)
        m = commit_re.match(line)
        if m:
            repo = m.group(1)
            commit = m.group(2)
        if import_re.match(line):
            break
    return module, repo, commit

# contains ported files
# lean 3 module name -> { mathlib4_file, mathlib3_hash }
data = dict()
for path4 in Path(mathlib4_root).glob('**/*.lean'):
    if path4.relative_to(mathlib4_root).parts[0] in \
       ['Init', 'Lean', 'Mathport', 'Tactic', 'Testing', 'Util']:
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
        'mathlib4_file': 'Mathlib/' + str(path4.relative_to(mathlib4_root)),
        'mathlib4_pr': mathlib4_pr,
        'source': dict(repo=repo, commit=commit)
    }

prs = {}
fetch_args = ['git', 'fetch', 'origin']
nums = []
mathlib4repo = github.Github(github_token).get_repo("leanprover-community/mathlib4")
for pr in mathlib4repo.get_pulls(state='open'):
    if pr.created_at < datetime.datetime(2022, 12, 1, 0, 0, 0):
        continue
    if 'no-source-header' in (l.name for l in pr.labels):
        continue
    num = pr.number
    nums.append(num)
    prs[num] = pr
    fetch_args.append(f'pull/{num}/head:port-status-pull/{num}')

os.system("git branch -D $(git branch --list 'port-status-pull/*')")
subprocess.run(fetch_args)

prs_of_condensed = {}
for num in nums:
    p = subprocess.run(
        ['git', 'diff', '--name-only', '--diff-filter=A',
         f'origin/master...port-status-pull/{num}'],
        capture_output=True)
    for l in p.stdout.decode().splitlines():
        f = subprocess.run(
            ['git', 'cat-file', 'blob', f'port-status-pull/{num}:{l}'],
            capture_output=True)
        _, repo, commit = get_mathlib4_module_commit_info(f.stdout.decode())
        prs_of_condensed.setdefault(condense(l), []).append({'pr': num, 'repo': repo, 'commit': commit, 'fname': l})

def pr_to_str(pr):
    labels = ' '.join(f'[{l.name}]' for l in pr.labels)
    return f'[#{pr.number}]({pr.html_url}) (by {pr.user.login}, {labels}, last activity {pr.updated_at})'

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
        pr_status = f"mathlib4#{data[node]['mathlib4_pr']}" if data[node]['mathlib4_pr'] is not None else "_"
        sha = data[node]['source']['commit'] if data[node]['source']['repo'] == 'leanprover-community/mathlib' else "_"
        
        status = f"Yes {pr_status} {sha}"
    else:
        new_status = dict(ported=False)
        status = f'No'
        if condense(node) in prs_of_condensed:
            pr_info = prs_of_condensed[condense(node)][0]
            if pr_info['commit'] is None:
                print('PR seems to be missing a source header', node, pr_info)
                assert(False)
            new_status.update(
                mathlib4_pr=pr_info['pr'],
                mathlib4_file=pr_info['fname'],
                source=dict(repo=pr_info['repo'], commit=pr_info['commit']))
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
