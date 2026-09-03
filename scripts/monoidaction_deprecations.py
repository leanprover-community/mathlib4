#!/usr/bin/env python3
"""Add deprecated aliases for every declaration renamed by the `MulAction` → `MonoidAction` move.

This is the second step of the rename described in `scripts/monoidaction_decls.py`.  It
inserts, directly below each renamed declaration, a shim under the declaration's old name:

    @[deprecated (since := "2026-09-02")] alias _root_.MulAction.orbit := orbit

Classes cannot be aliased -- `alias` produces a plain `def`, which Lean will not accept in an
instance binder -- so they get a reducible `abbrev` instead, which keeps binders, `extends`
clauses and instance synthesis working:

    @[deprecated MonoidAction (since := "2026-09-02")] abbrev _root_.MulAction := @MonoidAction

Which declarations exist, which of them `to_additive` generated, and where each one ends is read
out of a *pre-rename* Mathlib environment rather than guessed from the source, because the
additive halves of `to_additive` pairs have no source text of their own.  Run

    lake exe cache get && lake build          # on the commit *before* the rename
    python3 scripts/monoidaction_deprecations.py --dump-only

once to produce the data file, then run the script without `--dump-only` on the renamed tree.
"""

import argparse
import collections
import importlib.util
import os
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.dont_write_bytecode = True          # keep `scripts/` free of a `__pycache__` directory
_spec = importlib.util.spec_from_file_location("rename", HERE / "monoidaction_decls.py")
rename = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(rename)

DATA = pathlib.Path("monoidaction_dump.tsv")
DATE = "2026-09-02"
LINE_LIMIT = 100

# Declarations Lean generates for us; they follow their parent and need no shim.
AUTO_SUFFIXES = (".casesOn", ".recOn", ".brecOn", ".below", ".binductionOn", ".ibelow",
                 ".noConfusion", ".noConfusionType", ".ctorIdx", ".rec", ".mk", ".injEq",
                 ".sizeOf_spec", ".toCtorIdx", ".eq_def")
# `Foo.match_1`, `Foo.proof_2`, ... are lifted out of a declaration's elaboration.
AUTO_COMPONENT = re.compile(r"^(match|proof|eq|def|fun|lam)_[0-9]+$")

# Every declaration whose name mentions `Action` is dumped; the Python side picks out the ones
# this rename touches.  That keeps the dumper usable against a pre- *or* post-rename build.
DUMPER = r'''
import Mathlib

open Lean in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let s := n.toString
    if (s.splitOn "Action").length == 1 then continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | _ => "def"
    let mod := match env.getModuleFor? n with | some m => m.toString | none => ""
    let depr := Lean.Linter.isDeprecated env n
    let prot := Lean.isProtected env n
    let some rg ← Lean.findDeclarationRanges? n | continue
    out := out.push s!"{s}\t{kind}\t{mod}\t{rg.range.pos.line}\t{rg.range.endPos.line}\t\
      {if depr then "depr" else "-"}\t{if prot then "prot" else "-"}"
  IO.FS.writeFile "monoidaction_dump.tsv" (String.intercalate "\n" out.qsort.toList)
'''

# The rename is a bijection: no declaration mentioned `MonoidAction` before it, and none
# mentions `MulAction` (outside the protected names) after it.  So the dump can be read either
# way round, and the script works whichever build produced it.
UNRENAMES = [("AddMonoidAction", "AddAction"), ("addMonoidAction", "addAction"),
             ("MonoidAction", "MulAction"), ("monoidAction", "mulAction")]


def old_and_new(name):
    """Return `(old, new)` for a name from either side of the rename, or `None`."""
    renamed = rename.convert(name)
    if renamed != name:
        return name, renamed
    unrenamed = name
    for new, old in UNRENAMES:
        unrenamed = unrenamed.replace(new, old)
    if unrenamed != name:
        return unrenamed, name
    return None


def dump():
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(DUMPER)
        path = f.name
    try:
        subprocess.run(["lake", "env", "lean", path], check=True)
    finally:
        os.unlink(path)
    print(f"wrote {DATA} ({sum(1 for _ in open(DATA))} declarations)", file=sys.stderr)


def is_auto(name):
    """Lean-generated declarations, and instances whose names Lean chose."""
    return (name.endswith(AUTO_SUFFIXES)
            or any(AUTO_COMPONENT.match(part) for part in name.split("."))
            or name.split(".")[-1].startswith("inst"))


# ---------------------------------------------------------------------------
# Namespace tracking, so that the shim is declared under its old *root* name
# ---------------------------------------------------------------------------

NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*$")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section\b")
END_RE = re.compile(r"^end\b")


def comment_mask(lines):
    """Whether each line starts inside a `/- ... -/` block comment or docstring."""
    out, depth = [], 0
    for line in lines:
        out.append(depth > 0)
        i = 0
        while i < len(line) - 1:
            pair = line[i:i + 2]
            if depth == 0 and pair == "--":
                break
            if pair == "/-":
                depth += 1
            elif pair == "-/":
                depth = max(0, depth - 1)
            else:
                i += 1
                continue
            i += 2
    return out


def insertion_point(lines, comments, decl_end):
    """The line index at which a shim for a declaration ending at `decl_end` should be spliced.

    `decl_end` is only a hint: Lean reports sub-syntax for declarations it generated itself, so
    an `ext` lemma points at the `ext` token inside the attribute and a structure field points
    at the field.  Splicing there would land inside the command, so instead walk forward to the
    end of the enclosing command -- the blank line before the next top-level command, or the
    `end` that closes the surrounding namespace, whichever comes first.  Blank lines inside a
    docstring do not count, or the shim would be swallowed by the doc comment.
    """
    i = max(decl_end, 0)
    while i < len(lines):
        if comments[i]:                 # a blank line inside a docstring is not a boundary
            i += 1
            continue
        if lines[i].startswith("end") or lines[i].startswith("/-!"):
            return i
        if not lines[i].strip():
            nxt = next((j for j in range(i + 1, len(lines))
                        if lines[j].strip() and not comments[j]), None)
            if nxt is None or not lines[nxt][:1].isspace():
                return i
        i += 1
    return len(lines)


def namespaces_by_line(lines, comments):
    """For each 0-based line, the namespace open at that point."""
    stack, out = [], []
    for line, in_comment in zip(lines, comments):
        out.append(".".join(n for n in stack if n is not None))
        if in_comment:
            continue
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(m.group(1))
        elif SECTION_RE.match(line):
            stack.append(None)
        elif END_RE.match(line) and stack:
            stack.pop()
    out.append(".".join(n for n in stack if n is not None))
    return out


def relative(new_name, namespace, spell_out):
    """Spell `new_name` as it should be written inside `namespace`."""
    if namespace and not spell_out and (new_name + ".").startswith(namespace + "."):
        return new_name[len(namespace) + 1:]
    return ("_root_." + new_name) if namespace else new_name


def shim(old, new, namespace, is_class, is_protected):
    lhs = ("_root_." + old) if namespace else old
    # A `protected` declaration is not in scope under its short name even inside its own
    # namespace.  And an `abbrev` has its own short name in scope in its body, so a class shim
    # abbreviating a same-named class would refer to itself; both need the full name.
    rhs = relative(new, namespace, is_protected or is_class)
    if is_class:
        # Unlike `alias`, an `abbrev` is subject to the `docBlame` linter.
        doc = [f"/-- Deprecated alias for `{new}`. -/"]
        head = f"@[deprecated {rhs} (since := \"{DATE}\")]"
        body = f"abbrev {lhs} := @{rhs}"
        if len(head) + 1 + len(body) <= LINE_LIMIT:
            return doc + [head + " " + body]
        if len(body) <= LINE_LIMIT:
            return doc + [head, body]
        return doc + [head, f"abbrev {lhs} :=", "  @" + rhs]
    else:
        head = f"@[deprecated (since := \"{DATE}\")]"
        body = f"alias {lhs} := {rhs}"
    if len(head) + 1 + len(body) <= LINE_LIMIT:
        return [head + " " + body]
    if len(body) <= LINE_LIMIT:
        return [head, body]
    keyword, rest = body.split(" ", 1)
    return [head, f"{keyword} {lhs} :=", "  " + rhs]


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dump-only", action="store_true",
                        help="only regenerate the declaration data from a pre-rename build")
    args = parser.parse_args()

    if args.dump_only or not DATA.exists():
        dump()
        if args.dump_only:
            return

    per_file = collections.defaultdict(list)
    skipped = []
    for row in DATA.read_text(encoding="utf-8").split("\n"):
        if not row.strip():
            continue
        name, kind, module, _start, end, depr, prot = row.split("\t")
        pair = old_and_new(name)
        if pair is None or kind in ("ctor", "rec") or is_auto(name):
            continue
        old, new = pair
        if depr == "depr":
            continue        # already deprecated under its old name; no second hop
        if not module:
            skipped.append(old)
            continue
        path = pathlib.Path(module.replace(".", "/") + ".lean")
        if not path.exists():
            skipped.append(old)
            continue
        per_file[path].append((int(end), old, new, kind == "induct", prot == "prot"))

    total = 0
    for path, entries in sorted(per_file.items()):
        lines = path.read_text(encoding="utf-8").split("\n")
        comments = comment_mask(lines)
        spaces = namespaces_by_line(lines, comments)
        groups = collections.defaultdict(list)
        for end, old, new, is_class, is_protected in entries:
            at = insertion_point(lines, comments, end)
            groups[at].append((old, new, is_class, is_protected))
        # Insert from the bottom so earlier line numbers stay valid.
        for at in sorted(groups, reverse=True):
            namespace = spaces[min(at, len(spaces) - 1)]
            block = []
            # The multiplicative shim comes first, as it does for the declarations themselves.
            for old, new, is_class, is_protected in sorted(
                    groups[at], key=lambda e: ("AddMonoidAction" in e[1]
                                               or "addMonoidAction" in e[1], e[0])):
                block += shim(old, new, namespace, is_class, is_protected)
                total += 1
            after = [""] + block
            if at < len(lines) and lines[at].strip():
                after.append("")
            lines[at:at] = after
        if lines[-1]:                   # a shim spliced at EOF must not eat the final newline
            lines.append("")
        path.write_text("\n".join(lines), encoding="utf-8")

    print(f"added {total} deprecations across {len(per_file)} files", file=sys.stderr)
    if skipped:
        print(f"skipped {len(skipped)} declarations with no source location:", file=sys.stderr)
        for name in skipped[:20]:
            print("  " + name, file=sys.stderr)


if __name__ == "__main__":
    main()
