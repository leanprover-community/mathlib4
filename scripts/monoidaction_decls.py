#!/usr/bin/env python3
"""Rename only the *declaration sites* of the `MulAction` -> `MonoidAction` move.

    python3 scripts/monoidaction_decls.py

Renames the name a declaration introduces, `namespace`/`end`, `extends` parents (which
introduce a `toFoo` projection) and the explicit name argument of `to_additive` -- and nothing
else, so the result does not build.  The use sites follow later, with

    find Mathlib Archive Counterexamples MathlibTest Wanted -name '*.lean' -print0 \
      | xargs -0 sed -i -f scripts/monoidaction_rename.sed

`monoidaction_rename.sed` is the single source of truth for what is renamed and what is left
alone; the substitutions are read out of it below.
"""

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOTS = ["Mathlib", "Archive", "Counterexamples", "MathlibTest", "Wanted"]
# Files outside the Lean sources that refer to declarations by name.
EXTRA_FILES = ["docs/1000.yaml", "docs/overview.yaml", "docs/undergrad.yaml",
               "scripts/nolints.json"]


def _table():
    """The `s/old/new/g` lines of the sed script, in order."""
    subs = []
    for line in (HERE / "monoidaction_rename.sed").read_text(encoding="utf-8").splitlines():
        if line.startswith("s/"):
            old, new = line[2:-2].split("/")
            subs.append((old.replace(r"\.", "."), new))
    return subs


SUBS = _table()


def convert(text):
    for old, new in SUBS:
        text = text.replace(old, new)
    return text


ATTRS = r"(?:@\[[^\]]*\]\s*)*"
MODIFIERS = r"(?:(?:private|protected|noncomputable|scoped|local|partial|unsafe|nonrec)\s+)*"
DECL_KW = (r"(?:theorem|lemma|def|abbrev|instance|class\s+abbrev|class|structure|inductive"
           r"|alias|opaque|axiom)")
CONFIG = r"(?:\([^)]*\)\s*)?"                       # `instance (priority := 100) foo`
# The declared name: up to whitespace or the start of the binders, type or value.
DECL_RE = re.compile(r"^(\s*" + ATTRS + MODIFIERS + DECL_KW + r"\s+" + CONFIG + r")"
                     r"((?:_root_\.)?[^\s:={(\[]+)")
NS_RE = re.compile(r"^(\s*(?:namespace|end)\s+)(\S+)(\s*)$")
EXTENDS_RE = re.compile(r"^(.*\bextends\s+)(.*)$")
# `@[to_additive AddFoo]` names the declaration `to_additive` is about to create.  The name may
# follow `existing` and/or option groups such as `(attr := simp)`, and may sit on its own line.
TO_ADDITIVE_RE = re.compile(r"(\bto_(?:additive|dual)\s+(?:(?:existing|\([^)]*\))\s+)*)"
                            r"([A-Za-z_][\w'.]*)")


def rename_decls(text):
    out = []
    for line in text.split("\n"):
        m = DECL_RE.match(line)
        if m:
            line = m.group(1) + convert(m.group(2)) + line[m.end(2):]
        m = NS_RE.match(line)
        if m:
            line = m.group(1) + convert(m.group(2)) + m.group(3)
        # A backtick means the `extends` is inside a docstring or a comment, not a header.
        if "`" not in line:
            m = EXTENDS_RE.match(line)
            if m:
                line = m.group(1) + convert(m.group(2))
        out.append(line)
    # Run over the whole text so a `to_additive` name on a continuation line is caught too.
    return TO_ADDITIVE_RE.sub(lambda m: m.group(1) + convert(m.group(2)), "\n".join(out))


def main():
    changed = 0
    paths = [p for root in ROOTS for p in sorted(pathlib.Path(root).rglob("*.lean"))]
    paths += [p for p in map(pathlib.Path, EXTRA_FILES) if p.exists()]
    for path in paths:
        old = path.read_text(encoding="utf-8")
        # Name references in `docs/*.yaml` and `nolints.json` follow the declarations.
        new = rename_decls(old) if path.suffix == ".lean" else convert(old)
        if new != old:
            path.write_text(new, encoding="utf-8")
            changed += 1
    print(f"rewrote {changed} files", file=sys.stderr)


if __name__ == "__main__":
    main()
