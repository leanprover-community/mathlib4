#!/usr/bin/env python3

import sys
import os
import subprocess
import re

if len(sys.argv) != 2 or not sys.argv[1].endswith('.lean'):
    print("usage: fix-lints.py X.lean")
    sys.exit(1)

leanfile = sys.argv[1]

root_dir = subprocess.run(
    ['git', 'rev-parse', '--show-toplevel'],
    capture_output=True).stdout.decode().rstrip()

prefix = subprocess.run(
    ['git', 'rev-parse', '--show-prefix'],
    capture_output=True).stdout.decode().rstrip()

align_files = subprocess.run(
    ['git', 'grep', '-l', '^#align'],
    cwd=root_dir,
    capture_output=True)

name_map = dict()
for f in align_files.stdout.decode().splitlines():
    contents = open(f).read()
    for p in contents.split(sep='\n#align')[1:]:
        n3, n4, *_ = p.split(maxsplit=2)
        name_map[n3] = n4

def replace_names(s):
    # re.DOTALL means that `.` can also match a newline.
    # `\A` and `\Z` match only at the start/end of the string respectively.
    w = re.findall(r'(?:\b|\A).+?(?:\b|\Z)', s, flags=re.DOTALL)
    for i in range(len(w)):
        w[i] = name_map.get(w[i], w[i])
    return ''.join(w)

def process_backticked_names(s):
    w = s.split(sep='`')
    for i in range(len(w)):
        if i % 2 == 1:
            w[i] = replace_names(w[i])
    return '`'.join(w)

tmpfile = leanfile + '.bak'
tmp = open(tmpfile, 'w')

in_block_comment = False
in_line_comment = False
prev_char = None
comment_so_far = None           # contains end marker but not begin marker

def finish_comment():
    global in_block_comment
    global in_line_comment
    global comment_so_far
    if comment_so_far is not None:
        tmp.write(process_backticked_names(comment_so_far))
        in_block_comment = False
        in_line_comment = False
        comment_so_far = None

with open(leanfile) as F:
    while 1:
        char = F.read(1)
        if not char:
            finish_comment()
            break

        if in_block_comment or in_line_comment:
            comment_so_far = comment_so_far + char
        else:
            tmp.write(char)

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

tmp.close()

def mktree(reversed_path_list, sha, tree=True):
    if reversed_path_list == []:
        return sha
    hd, *tl = reversed_path_list
    if tree:
        inp = f"040000 tree {sha}\t{hd}"
    else:
        inp = f"100644 blob {sha}\t{hd}"
    tree_sha = subprocess.run(
        ['git', 'mktree'],
        cwd=root_dir,
        input=inp.encode('utf-8'),
        capture_output=True).stdout.decode().rstrip()
    return mktree(tl, tree_sha)

if prefix == '':
    tmpfile_wrt_root = tmpfile
    path_list = leanfile.split(sep='/')
else:
    tmpfile_wrt_root = prefix + '/' + tmpfile
    path_list = prefix.split(sep='/') + leanfile.split(sep='/')

blob_sha = subprocess.run(
    ['git', 'hash-object', '-w', tmpfile_wrt_root],
    cwd=root_dir,
    capture_output=True).stdout.decode().rstrip()

tree_sha = mktree(reversed(path_list), blob_sha, tree=False)

subprocess.run(['git', 'restore', '-p', '-s', tree_sha, '--', leanfile])

os.remove(tmpfile)
