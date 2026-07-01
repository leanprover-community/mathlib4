#!/usr/bin/env python3
"""Remove Lean imports that are already available through another direct import.

This is a graph-only tool: it reads import declarations, builds the import DAG, and
does not inspect Lean declarations or run minimization builds.
"""

from __future__ import annotations

import argparse
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO_ROOT / "Mathlib"


@dataclass(frozen=True)
class ImportLine:
    line_number: int
    module: str
    public: bool
    meta: bool
    all_private: bool
    keep: bool


@dataclass
class LeanFile:
    path: Path
    module: str
    imports: list[ImportLine]
    keep_all: bool
    lines: list[str]


@dataclass(frozen=True)
class RedundantImport:
    path: Path
    line_number: int
    module: str


def module_name(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT).with_suffix("")
    return ".".join(rel.parts)


def path_from_arg(arg: str) -> Path:
    path = Path(arg)
    if not path.is_absolute():
        path = REPO_ROOT / path
    return path


def is_excluded(path: Path) -> bool:
    rel_parts = path.relative_to(REPO_ROOT).parts
    return ".lake" in rel_parts or (rel_parts and rel_parts[0] == "MathlibTest")


def discover_files(args: list[str]) -> list[Path]:
    roots = [path_from_arg(arg) for arg in args] if args else [DEFAULT_ROOT]
    files: list[Path] = []
    for root in roots:
        if not root.exists():
            raise FileNotFoundError(root)
        if root.is_file():
            if root.suffix == ".lean" and not is_excluded(root):
                files.append(root)
            continue
        files.extend(path for path in root.rglob("*.lean") if not is_excluded(path))
    return sorted(set(files))


def strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def parse_import_line(line: str, line_number: int) -> ImportLine | None:
    code = strip_line_comment(line).strip()
    if not code:
        return None
    tokens = code.split()
    public = False
    meta = False
    all_private = False
    i = 0
    while i < len(tokens) and tokens[i] in {"public", "meta"}:
        public = public or tokens[i] == "public"
        meta = meta or tokens[i] == "meta"
        i += 1
    if i >= len(tokens) or tokens[i] != "import":
        return None
    i += 1
    if i < len(tokens) and tokens[i] == "all":
        all_private = True
        i += 1
    if i >= len(tokens):
        return None
    module = tokens[i]
    if not module.replace(".", "").replace("_", "").isalnum():
        return None
    return ImportLine(
        line_number=line_number,
        module=module,
        public=public,
        meta=meta,
        all_private=all_private,
        keep="shake: keep" in line,
    )


def parse_file(path: Path) -> LeanFile:
    lines = path.read_text().splitlines(keepends=True)
    imports: list[ImportLine] = []
    keep_all = any("shake: keep-all" in line for line in lines)
    in_block_comment = False
    seen_module = False

    for line_number, line in enumerate(lines, start=1):
        stripped = line.strip()
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("/-"):
            in_block_comment = "-/" not in stripped
            continue
        if not stripped or stripped.startswith("--"):
            continue
        if stripped == "module":
            seen_module = True
            continue

        imp = parse_import_line(line, line_number)
        if imp is not None:
            imports.append(imp)
            continue

        if seen_module or imports:
            break

    return LeanFile(
        path=path,
        module=module_name(path),
        imports=imports,
        keep_all=keep_all,
        lines=lines,
    )


def build_graph(
    files: list[LeanFile],
    *,
    public_only: bool = False,
    nonmeta_only: bool = False,
) -> dict[str, set[str]]:
    known = {lean_file.module for lean_file in files}
    graph: dict[str, set[str]] = {module: set() for module in known}
    for lean_file in files:
        for imp in lean_file.imports:
            if imp.module not in known:
                continue
            if public_only and not imp.public:
                continue
            if nonmeta_only and imp.meta:
                continue
            if imp.all_private:
                continue
            graph[lean_file.module].add(imp.module)
    return graph


def compute_reachability(graph: dict[str, set[str]]):
    memo: dict[str, set[str]] = {}

    def reachable(module: str) -> set[str]:
        if module in memo:
            return memo[module]
        result: set[str] = set()
        for child in graph.get(module, set()):
            result.add(child)
            result.update(reachable(child))
        memo[module] = result
        return result

    return reachable


def find_redundant_imports(files: list[LeanFile]) -> list[RedundantImport]:
    public_nonmeta_graph = build_graph(files, public_only=True, nonmeta_only=True)
    public_nonmeta_reachable = compute_reachability(public_nonmeta_graph)
    redundant: list[RedundantImport] = []

    for lean_file in files:
        if lean_file.keep_all:
            continue
        for candidate in lean_file.imports:
            if candidate.keep or candidate.meta or candidate.all_private:
                continue
            for other in lean_file.imports:
                if other is candidate or other.meta or other.all_private:
                    continue
                if candidate.public and not other.public:
                    continue
                if candidate.module in public_nonmeta_reachable(other.module):
                    redundant.append(
                        RedundantImport(
                            path=lean_file.path,
                            line_number=candidate.line_number,
                            module=candidate.module,
                        )
                    )
                    break

    return redundant


def apply_removals(files: list[LeanFile], redundant: list[RedundantImport]) -> None:
    by_path: dict[Path, set[int]] = {}
    for item in redundant:
        by_path.setdefault(item.path, set()).add(item.line_number)

    files_by_path = {lean_file.path: lean_file for lean_file in files}
    for path, line_numbers in by_path.items():
        lean_file = files_by_path[path]
        new_lines = [
            line for idx, line in enumerate(lean_file.lines, start=1) if idx not in line_numbers
        ]
        path.write_text("".join(new_lines))


def check_fixture() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        mathlib = root / "Mathlib"
        (mathlib / "Doc").mkdir(parents=True)
        (mathlib / "A.lean").write_text(
            "\n".join(
                [
                    "module",
                    "",
                    "public import Mathlib.B",
                    "public import Mathlib.C",
                    "import Mathlib.D",
                    "import Mathlib.E",
                    "import Mathlib.Keep -- shake: keep",
                    "import all Mathlib.Private",
                    "",
                    "/--",
                    "import Mathlib.Doc.Example",
                    "-/",
                    "def x := 1",
                    "",
                ]
            )
        )
        (mathlib / "B.lean").write_text("module\n\npublic import Mathlib.C\n")
        (mathlib / "C.lean").write_text("module\n")
        (mathlib / "D.lean").write_text("module\n\npublic import Mathlib.E\n")
        (mathlib / "E.lean").write_text("module\n")
        (mathlib / "Keep.lean").write_text("module\n")
        (mathlib / "Private.lean").write_text("module\n\npublic import Mathlib.C\n")
        (mathlib / "Skip.lean").write_text("module -- shake: keep-all\n\npublic import Mathlib.C\n")

        old_root = globals()["REPO_ROOT"]
        try:
            globals()["REPO_ROOT"] = root
            files = [parse_file(path) for path in sorted(mathlib.rglob("*.lean"))]
            found = find_redundant_imports(files)
            got = {(item.path.name, item.module) for item in found}
            want = {("A.lean", "Mathlib.C"), ("A.lean", "Mathlib.E")}
            if got != want:
                raise AssertionError(f"got {got}, want {want}")
            apply_removals(files, found)
            rewritten = (mathlib / "A.lean").read_text()
            if "public import Mathlib.C" in rewritten or "import Mathlib.E" in rewritten:
                raise AssertionError("redundant imports were not removed")
            if "shake: keep" not in rewritten or "import all Mathlib.Private" not in rewritten:
                raise AssertionError("protected imports were removed")
        finally:
            globals()["REPO_ROOT"] = old_root

    print("fixture checks passed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="Lean files or directories to scan")
    parser.add_argument("--fix", action="store_true", help="rewrite files instead of dry-run report")
    parser.add_argument("--check-fixture", action="store_true", help="run embedded fixture tests")
    args = parser.parse_args()

    if args.check_fixture:
        check_fixture()
        return 0

    if not shutil.which("python3"):
        pass

    paths = discover_files(args.paths)
    files = [parse_file(path) for path in paths]
    redundant = find_redundant_imports(files)

    action = "removed" if args.fix else "removable"
    for item in redundant:
        rel = item.path.relative_to(REPO_ROOT)
        print(f"{rel}:{item.line_number}: {action} import {item.module}")

    if args.fix:
        apply_removals(files, redundant)
        print(f"Total redundant imports removed: {len(redundant)}")
    else:
        print(f"Total redundant imports found: {len(redundant)}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
