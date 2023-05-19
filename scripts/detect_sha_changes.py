"""
This script is called by a github action to verify that commit SHAs used in porting are valid.
It also produces links to the port-status webpage.

Note that only the first 10 annotations created with this action are guaranteed to appear, so we
produce the errors first.
"""

from dataclasses import dataclass
import re
import sys
from typing import Optional

import git

# upstream bug
git.Git.CatFileContentStream.__next__ = git.Git.CatFileContentStream.next

# from https://github.com/leanprover-community/mathlib4/blob/master/scripts/make_port_status.py#L83-L95
source_module_re = re.compile(r"^! .*source module (.*)$")
commit_re = re.compile(r"^! (leanprover-community/[a-z]*) commit ([0-9a-f]*)")
import_re = re.compile(r"^import ([^ ]*)")

@dataclass
class VersionInfo:
    module: str
    repo: Optional[str]
    commit: Optional[str]
    commit_line_no: Optional[int]

    def to_commit(self):
        try:
            repo = git.Repo('port-repos/' + self.repo)
        except git.exc.NoSuchPathError:
            raise ValueError(f"Repo {self.repo} not recognized")
        try:
            repo.remotes.origin.fetch(self.commit, depth=1)
        except Exception:
            pass
        return repo.commit(self.commit)

def get_mathlib4_module_commit_info(contents):
    module = repo = commit = None
    commit_line_no = 0
    for i, line in enumerate(contents, 1):
        m = source_module_re.match(line)
        if m:
            module = m.group(1)
        m = commit_re.match(line)
        if m:
            repo = m.group(1)
            commit = m.group(2)
            commit_line_no = i
        if import_re.match(line):
            break
    if module is None:
        raise ValueError("No module info")
    return VersionInfo(module, repo, commit, commit_line_no)

def get_mathlib4_module_commit_info_from_blob(blob: Optional[git.Blob]):
    if blob is None:
        return None
    try:
        return get_mathlib4_module_commit_info(
            l.decode('utf8') for l in blob.data_stream.stream)
    except ValueError:
        return None

def encode_msg_text_for_github(msg):
    # even though this is probably url quoting, we match the implementation at
    # https://github.com/actions/toolkit/blob/af821474235d3c5e1f49cee7c6cf636abb0874c4/packages/core/src/command.ts#L36-L94
    return msg.replace('%', '%25').replace('\r', '%0D').replace('\n', '%0A')

if __name__ == '__main__':
    repo = git.Repo('.')
    base = repo.commit(sys.argv[1])
    head = repo.commit(sys.argv[2])
    any_errors = False

    diff_infos = []
    for diff in base.diff(head, paths=['Mathlib']):
        a_info = get_mathlib4_module_commit_info_from_blob(diff.a_blob)
        b_info = get_mathlib4_module_commit_info_from_blob(diff.b_blob)
        if a_info == b_info or b_info is None:
            continue
        diff_infos.append((diff, a_info, b_info))

    all_refs = {}

    # produce errors first
    for diff, a_info, b_info in diff_infos:
        if b_info:
            try:
                b_info.to_commit()
            except Exception as e:
                print(f"::error file={diff.b_blob.path},line={b_info.commit_line_no},title=Invalid header::{encode_msg_text_for_github(str(e))}")
                any_errors = True
                continue

    for diff, a_info, b_info in diff_infos:
        if a_info is not None and b_info is not None:
            if a_info.module == b_info.module:
                mod_path = a_info.module.replace('.', '/')
                msg = f"See https://leanprover-community.github.io/mathlib-port-status/file/{mod_path}?range={a_info.commit}..{b_info.commit}"
                print(f"::notice file={diff.b_blob.path},line={b_info.commit_line_no},title=Synchronization::{msg}")
            else:
                print(f"::warning file={diff.b_blob.path},line={b_info.commit_line_no},title=Filename changed!::{a_info} -> {b_info}")

    if any_errors:
        raise SystemExit("Setting a failure due to errors above")
