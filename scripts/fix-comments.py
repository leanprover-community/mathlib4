#!/usr/bin/env python3

import sys
import os
from pathlib import Path
import subprocess
import re

if len(sys.argv) != 2 or not sys.argv[1].endswith('.lean'):
    print("usage: fix-comments.py X.lean")
    sys.exit(1)

leanfile = sys.argv[1]

is_clean = subprocess.run(
    ['git', 'status', '--untracked-files=no', '--porcelain'],
    capture_output=True,
    check=True,
    encoding='utf-8').stdout.rstrip()

if is_clean != "":
    print("Certain files tracked by git have uncommitted changes.\n")
    os.system("git status --untracked-files=no")
    print("\n")
    s = input("Type y to continue. ")
    if s != 'y':
        sys.exit(1)

root_dir = subprocess.run(
    ['git', 'rev-parse', '--show-toplevel'],
    capture_output=True,
    check=True,
    encoding='utf-8').stdout.rstrip()

align_files = subprocess.run(
    ['git', 'grep', '-l', '^#align'],
    cwd=root_dir,
    capture_output=True,
    check=True,
    encoding='utf-8')

name_map = dict()
for f in align_files.stdout.splitlines():
    with open(os.path.join(root_dir, f), encoding="utf-8") as fh:
        contents = fh.read()
        for p in contents.split(sep='\n#align')[1:]:
            n3, n4, *_ = p.split(maxsplit=2)
            name_map[n3] = n4

# Remove false positives: the following names are both Lean 3 and Lean 4 names,
# so do not replace these.
same = {
    'succ_nsmul', 'CommGroup', 'and_comm', 'Set.mem_singleton', "succ_nsmul'", 'Set.ext_iff',
    'not_ball', "mul_nsmul'", 'mul_nsmul', 'Set.mem_powerset', 'div_mul_cancel', 'Set.mem_sep',
    'or_assoc', 'Set.mem_insert_iff', 'and_assoc', 'Ring', 'AddSemigroup', 'add_sub_cancel',
    'Algebra', 'Set.mem_sInter', 'mul_div_cancel', 'Set.sUnion_empty', 'Set.ext', 'or_comm',
    'Set.range', 'Set.sUnion_pair', 'Set.mem_sUnion_of_mem', 'Set.sInter_empty', 'Set.mem_image',
    'Set.mem_insert_of_mem', "forall_apply_eq_imp_iff'", 'Group', 'AddCommGroup',
    'mul_div_cancel_left', 'Set.empty_subset', 'Fintype', 'Set.mem_union', 'pow_succ', 'Set.mem_prod',
    'Set.sUnion_singleton', 'forall_apply_eq_imp_iff', 'Cauchy', 'Module', "or_congr_left'",
    'Set.not_nonempty_empty', 'Set.mem_range', 'Set.mem_diff', 'Set.powerset', 'Set.not_mem_empty',
    'Set.mem_inter', "or_congr_right'", 'forall_eq_apply_imp_iff', 'UniformSpace', 'lim',
    'Set.singleton_injective', 'Set.mem_sUnion', 'GroupWithZero', 'xor', 'or_congr_left',
    'Set.sInter', "pow_succ'", 'or_congr_right', "measurable_quotient_mk'", 'Set.insert_nonempty',
    'forall_congr', 'Top', 'Set.nonempty_def', 'Set.mem_insert', 'Set.nonempty_of_mem',
    'Set.eq_empty_or_nonempty', 'Set.subset_def', 'CommRing', 'Set.sUnion', 'Set.image', 'Set.prod',
    'Semigroup', 'not_or', "forall_eq_apply_imp_iff'", 'Set.sInter_singleton', 'Set',
    'Set.singleton_nonempty', 'AddGroup'
}

for s in same:
    del name_map[s]


def replace_names(s):
    # Terrible hack to treat `.` as a word character
    # (to match qualified names)
    s = s.replace('.', 'Ᾰ')
    # re.DOTALL means that `.` can also match a newline.
    # `\A` and `\Z` match only at the start/end of the string respectively.
    w = re.findall(r'(?:\b|\A).+?(?:\b|\Z)', s, flags=re.DOTALL)
    for i in range(len(w)):
        w[i] = w[i].replace('Ᾰ', '.')
        w[i] = name_map.get(w[i], w[i])
    return ''.join(w)

def process_backticked_names(s):
    w = s.split(sep='`')
    for i in range(len(w)):
        if i % 2 == 1:
            w[i] = replace_names(w[i])
    return '`'.join(w)

rewritten_contents = ''

in_block_comment = False
in_line_comment = False
prev_char = None
comment_so_far = None           # contains end marker but not begin marker

def finish_comment():
    global rewritten_contents
    global in_block_comment
    global in_line_comment
    global comment_so_far
    if comment_so_far is not None:
        rewritten_contents += process_backticked_names(comment_so_far)
        in_block_comment = False
        in_line_comment = False
        comment_so_far = None

with open(leanfile, encoding="utf-8") as F:
    while 1:
        char = F.read(1)
        if not char:
            finish_comment()
            break

        if in_block_comment or in_line_comment:
            comment_so_far = comment_so_far + char
        else:
            rewritten_contents += char

        if in_block_comment and prev_char == '-' and char == '/':
            finish_comment()

        if in_line_comment and char == '\n':
            finish_comment()

        if comment_so_far is None and prev_char == '/' and char == '-':
            in_block_comment = True
            comment_so_far = ''

        if comment_so_far is None and prev_char == '-' and char == '-':
            in_line_comment = True
            comment_so_far = ''

        prev_char = char

def mktree(path, sha, tree=True):
    if path == Path('.'):
        return sha
    if tree:
        inp = f"040000 tree {sha}\t{path.name}"
    else:
        inp = f"100644 blob {sha}\t{path.name}"
    tree_sha = subprocess.run(
        ['git', 'mktree'],
        cwd=root_dir,
        input=inp,
        capture_output=True,
        check=True,
        encoding='utf8').stdout.rstrip()
    return mktree(path.parent, tree_sha)

path = Path(subprocess.run(
    ['git', 'ls-files', '--full-name', leanfile],
    capture_output=True,
    check=True,
    encoding='utf-8').stdout.rstrip())

blob_sha = subprocess.run(
    ['git', 'hash-object', '-w', '--stdin'],
    input=rewritten_contents,
    cwd=root_dir,
    capture_output=True,
    check=True,
    encoding='utf-8').stdout.rstrip()

tree_sha = mktree(path, blob_sha, tree=False)

print(f"The script will now interactively suggest changes to {leanfile}.\n")
# s = input("Type y to continue. ")
# if s != 'y':
#     sys.exit(1)

subprocess.run(['git', 'restore', '--patch', '--source=' + tree_sha, '--', leanfile], check=True)

r = subprocess.run(['git', 'diff', '--quiet', leanfile])
if r.returncode == 0:
    pass
elif r.returncode == 1:           # file was changed
    print("\nPerhaps you would now like to run:")
    print(f"git add {leanfile} && git commit -m 'auto: naming'")
else:
    # something went wrong
    r.check_returncode()
