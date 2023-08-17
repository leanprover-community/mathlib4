"""
This script is called by a github action to verify that commit SHAs used in porting are valid.
It also produces links to the port-status webpage.

Note that only the first 10 annotations created with this action are guaranteed to appear, so we
produce the errors first.
"""

import dataclasses
import re
import sys
from typing import Optional

import git

# upstream bug
git.Git.CatFileContentStream.__next__ = git.Git.CatFileContentStream.next

align_import_re = re.compile(
    r'^#align_import ([^ ]*) from "(leanprover-community/[a-z]*)" ?@ ?"([0-9a-f]*)"')

@dataclasses.dataclass(eq=True, frozen=True)
class VersionInfo:
    module: str
    repo: Optional[str]
    commit: Optional[str]
    commit_line_no: Optional[int] = dataclasses.field(compare=False)

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

def get_mathlib4_module_commit_infos(contents):
    for i, line in enumerate(contents, 1):
        m = align_import_re.match(line)
        if m:
            module = m.group(1)
            repo = m.group(2)
            commit = m.group(3)
            yield VersionInfo(module, repo, commit, i)

def get_mathlib4_module_commit_info_from_blob(blob: Optional[git.Blob]):
    if blob is None:
        return
    yield from get_mathlib4_module_commit_infos(
            l.decode('utf8') for l in blob.data_stream.stream)

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
        a_info = set(get_mathlib4_module_commit_info_from_blob(diff.a_blob))
        b_info = set(get_mathlib4_module_commit_info_from_blob(diff.b_blob))
        if b_info <= a_info:
            continue
        diff_infos.append((diff, a_info, b_info))

    all_refs = {}

    # produce errors first
    for diff, a_infos, b_infos in diff_infos:
        for b_info in b_infos:
            try:
                b_info.to_commit()
            except Exception as e:
                print(f"::error file={diff.b_blob.path},line={b_info.commit_line_no},title=Invalid header::{encode_msg_text_for_github(str(e))}")
                any_errors = True
                continue

    for diff, a_info, b_info in diff_infos:
        same = a_info.intersection(b_info)
        a_info -= same
        b_info -= same
        if a_info != {} and b_info != {}:
            a_info_by_mod = {a.module: a for a in a_info}
            b_info_by_mod = {b.module: b for b in b_info}
            for k in set(a_info_by_mod.keys()) | set(b_info_by_mod.keys()):
                a_info = a_info_by_mod.get(k, None)
                b_info = b_info_by_mod.get(k, None)
                if a_info is None or b_info is None:
                    pass
                elif a_info.module == b_info.module:
                    mod_path = a_info.module.replace('.', '/')
                    msg = f"See review instructions and diff at\nhttps://leanprover-community.github.io/mathlib-port-status/file/{mod_path}?range={a_info.commit}..{b_info.commit}"
                    print(f"::notice file={diff.b_blob.path},line={b_info.commit_line_no},title=Synchronization::{encode_msg_text_for_github(msg)}")

    if any_errors:
        raise SystemExit("Setting a failure due to errors above")
