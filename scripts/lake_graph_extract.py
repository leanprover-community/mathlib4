#!/usr/bin/env python3
"""Extract mathlib4's Lake build graph as a static (command, inputs, outputs) DAG.

See lake_build_graph_analysis.md for the design rationale. This is the v0:
single-module emission + command-level validation. Larger scope (whole project,
output-level validation, cc_compile/cc_link nodes) lives in subsequent versions.

v0 strategy
-----------
Workspace-uniform constants (LEAN_PATH, toolchain path, packages list) are
captured empirically once and treated as static. Per-module variability
(transitive imports, source path, output paths, setup.json) is derived. The
setup.json *content* is currently obtained from ``lake setup-file <M>`` as an
oracle: it is the field most likely to drift if upstream packages change, and
v0 wants to validate the command template independently of the setup-derivation
logic. v1 will replace the oracle with static derivation from the lakefile +
import graph and will diff its output against the oracle as a regression test.

Sub-commands
------------
- emit            : write a single-module node to stdout (debugging aid)
- validate-commands <module> : run ``lake build -v`` on the module and byte-diff
                                the captured trace against the extracted command

Path conventions (relativized in emitted JSON; absolutized for validation)
-------------------------------------------------------------------------
$WORKSPACE   : project root (e.g. /Users/chelo/mathlib4)
$LAKE_HOME   : $WORKSPACE/.lake (cache, packages)
$TOOLCHAIN   : the toolchain bin dir derived from ``lake env lean``
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional

# --- Workspace constants (captured empirically; verified by --validate-commands)

WORKSPACE = Path("/Users/chelo/mathlib4").resolve()
LAKE_HOME = WORKSPACE / ".lake"
PACKAGES_DIR = LAKE_HOME / "packages"

# Order observed in `lake build -v` LEAN_PATH (see lake_build_graph_analysis.md
# §5.1, §5.3 and the Mathlib.Init capture). LEAN_PATH is workspace-static —
# every module of every package gets the same one. The order is Lake's
# topological resolution; rather than re-implement it we lift it verbatim.
LEAN_PATH_PACKAGES = [
    "Cli",                # transitive (via importGraph)
    "batteries",          # direct mathlib deps in lakefile order:
    "Qq",
    "aesop",
    "proofwidgets",
    "importGraph",
    "LeanSearchClient",
    "plausible",
]

# Lean libraries declared in mathlib's lakefile.lean (see §5 of the analysis)
# plus the upstream packages' lakefile.tomls. Each entry says:
#   pkg_dir : where the package lives ("" = mathlib root, "<name>" = .lake/packages/<name>)
#   srcDir  : the package-relative source directory (default: "")
#   leanOptions : the canonical options dict (oracle-fetched once per lib)
@dataclass
class LibConfig:
    pkg: str           # "mathlib" or upstream package name
    name: str          # lean_lib name
    pkg_dir: Path      # absolute pkg dir (mathlib root or .lake/packages/<pkg>)
    src_dir: Path      # absolute source root (= pkg_dir / srcDir)
    build_dir: Path    # absolute .lake/build dir for this package


def package_dirs() -> dict[str, Path]:
    """Return map pkg-name -> absolute package directory.

    Only includes packages listed in ``lake-manifest.json`` — Lake's authoritative
    record of resolved dependencies. Stale subdirectories left by prior versions
    of dependencies (e.g. ``lean4-cli`` when the active name is ``Cli``) are
    filtered out so they don't pollute the module registry with phantom files.
    """
    out: dict[str, Path] = {"mathlib": WORKSPACE}
    manifest_path = WORKSPACE / "lake-manifest.json"
    if not manifest_path.exists():
        raise RuntimeError(f"lake-manifest.json not found at {manifest_path}")
    manifest = json.loads(manifest_path.read_text())
    for entry in manifest.get("packages", []):
        name = entry["name"]
        candidate = PACKAGES_DIR / name
        if not candidate.is_dir():
            raise RuntimeError(
                f"package {name!r} listed in lake-manifest but directory not "
                f"found at {candidate}"
            )
        out[name] = candidate
    return out


def find_module_source(
    module: str, packages: dict[str, Path],
) -> tuple[str, Path]:
    """Locate ``module``'s source file across all packages.

    Returns (pkg_name, absolute_src_path). Mathlib is searched first so its
    own modules win (none of mathlib's lean_libs use a non-default srcDir).
    Raises FileNotFoundError if the module's source can't be found.
    """
    rel = module_to_relpath(module)
    # mathlib first
    candidate = packages["mathlib"] / rel
    if candidate.is_file():
        return "mathlib", candidate
    # then upstream packages, in deterministic order
    for pkg_name, pkg_dir in packages.items():
        if pkg_name == "mathlib":
            continue
        candidate = pkg_dir / rel
        if candidate.is_file():
            return pkg_name, candidate
    raise FileNotFoundError(
        f"Could not locate source for module {module!r} under "
        f"{', '.join(str(p) for p in packages.values())}"
    )


# ---------------------------------------------------------------------------
# Toolchain discovery
# ---------------------------------------------------------------------------

def discover_lean_binary() -> Path:
    """Resolve the lean binary that ``lake env`` would invoke."""
    res = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    # `lean --version` prints e.g. "Lean (version 4.30.0-rc2, ...)" — we don't
    # actually parse it; we just need the *path* to the binary, which we ask
    # the shell to find via `lake env`.
    res = subprocess.run(
        ["lake", "env", "sh", "-c", "command -v lean"],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    return Path(res.stdout.strip())


# ---------------------------------------------------------------------------
# Path helpers (module name <-> filesystem)
# ---------------------------------------------------------------------------

def module_to_relpath(module: str) -> Path:
    """``Mathlib.Init`` -> ``Mathlib/Init.lean`` (suffix added by caller)."""
    return Path(*module.split(".")).with_suffix(".lean")


_VALID_LEAN_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def lean_name_repr(module: str) -> str:
    """Serialize a dotted module name the way Lake does in setup.json.

    Lake parses the ``name`` field as a Lean ``Name``, so segments that aren't
    valid identifiers (e.g. ``check-yaml``) must be wrapped in French
    guillemets ``«...»``. Valid-identifier segments stay literal.
    """
    return ".".join(
        seg if _VALID_LEAN_IDENT.match(seg) else f"«{seg}»"
        for seg in module.split(".")
    )


# ---------------------------------------------------------------------------
# setup-file oracle
# ---------------------------------------------------------------------------

def lake_setup_file(module_lean_path: Path) -> dict:
    """Return the parsed setup.json that ``lake setup-file <p>`` produces.

    `module_lean_path` must be a path Lake recognizes. For mathlib's own
    modules pass the relative path (e.g. ``Mathlib/Init.lean``); for upstream
    pass the absolute path under .lake/packages.
    """
    res = subprocess.run(
        ["lake", "setup-file", str(module_lean_path)],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    return json.loads(res.stdout)


# ---------------------------------------------------------------------------
# Per-package lean_lib discovery (parsing what we strictly need)
# ---------------------------------------------------------------------------

def parse_mathlib_lakefile_libs() -> dict[str, dict]:
    """Return name -> {srcDir, root, globs, leanOptions_canonical=None}.

    We do not elaborate Lake; we read literal declarations from the source.
    leanOptions are filled in later via lake setup-file.
    """
    text = (WORKSPACE / "lakefile.lean").read_text()
    libs: dict[str, dict] = {}
    # crude but sufficient — mathlib's lakefile is regular
    for match in re.finditer(
        r"lean_lib\s+(?:\W*)([A-Za-z_][A-Za-z_0-9]*|«[^»]+»)\s+where\b([^\n]*(?:\n(?![a-zA-Z@/]).*)*)",
        text,
    ):
        raw_name = match.group(1)
        name = raw_name.strip("«»")
        body = match.group(2)
        libs[name] = {"raw": body}
    return libs


# ---------------------------------------------------------------------------
# Build an extracted node for a single module
# ---------------------------------------------------------------------------

@dataclass
class ExtractedNode:
    id: str
    kind: str  # "lean_module" for v0
    command: list[str]
    env: dict[str, str]
    inputs: list[dict]   # [{path, sha256?}]
    outputs: list[str]
    setup_json: dict


def _abs_path(p: str | Path) -> str:
    return str(Path(p).resolve())


def lean_path_string(packages: dict[str, Path]) -> str:
    """Build the ':'-joined LEAN_PATH for a mathlib module build."""
    parts: list[str] = []
    for pkg_name in LEAN_PATH_PACKAGES:
        if pkg_name not in packages:
            raise RuntimeError(
                f"Expected package '{pkg_name}' under {PACKAGES_DIR} "
                f"(LEAN_PATH order is empirically captured; if a package was "
                f"renamed/removed re-capture via `lake build -v`)"
            )
        parts.append(str(packages[pkg_name] / ".lake" / "build" / "lib" / "lean"))
    parts.append(str(WORKSPACE / ".lake" / "build" / "lib" / "lean"))
    return ":".join(parts)


def lean_module_node(
    module: str,
    *,
    lean_bin: Path,
    packages: dict[str, Path],
) -> ExtractedNode:
    """Build the node for a Lean module in any package."""
    pkg_name, src = find_module_source(module, packages)
    pkg_dir = packages[pkg_name]
    rel = module_to_relpath(module)

    # `lake setup-file` accepts either an absolute path or a workspace-relative
    # path. Absolute always works regardless of which package the module lives in.
    setup = lake_setup_file(src)

    lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir_dir = pkg_dir / ".lake" / "build" / "ir"

    olean       = lib_dir / rel.with_suffix(".olean")
    ilean       = lib_dir / rel.with_suffix(".ilean")
    olean_srv   = lib_dir / rel.with_suffix(".olean.server")
    olean_priv  = lib_dir / rel.with_suffix(".olean.private")
    ir          = lib_dir / rel.with_suffix(".ir")
    c           = ir_dir  / rel.with_suffix(".c")
    setup_path  = ir_dir  / rel.with_suffix(".setup.json")

    command = [
        str(lean_bin),
        str(src),
        "-o", str(olean),
        "-i", str(ilean),
        "-c", str(c),
        "--setup", str(setup_path),
        "--json",
    ]
    env = {"LEAN_PATH": lean_path_string(packages)}

    # v0 inputs: source + setup.json + transitive importArts (paths only; sha256
    # left empty — populated when CAS-ready emission is added).
    inputs: list[dict] = [{"path": str(src)}, {"path": str(setup_path)}]
    for art_module, paths in setup.get("importArts", {}).items():
        for p in paths:
            inputs.append({"path": p, "module": art_module})

    outputs = [
        str(olean), str(ilean), str(olean_srv), str(olean_priv),
        str(ir), str(c), str(setup_path),
    ]
    if setup.get("isModule"):
        # already covered above; module-style adds .olean.server, .olean.private, .ir
        pass

    return ExtractedNode(
        id=f"{pkg_name}:{module}",
        kind="lean_module",
        command=command,
        env=env,
        inputs=inputs,
        outputs=outputs,
        setup_json=setup,
    )


# ---------------------------------------------------------------------------
# Validation: run lake build -v, capture trace, diff
# ---------------------------------------------------------------------------

TRACE_PREFIX = "trace: .> "

def _capture_lake_trace_for_module(module: str) -> str:
    """Force a rebuild of `module` and return its `trace: .>` argv line.

    The module's olean+sidecars are deleted first so Lake actually re-invokes
    `lean`; otherwise it would `Replay` the cached artifact and emit no trace.
    Works for cross-package modules — artifacts are deleted in the *owning*
    package's build dir.
    """
    packages = package_dirs()
    pkg_name, src = find_module_source(module, packages)
    pkg_dir = packages[pkg_name]
    rel = module_to_relpath(module)
    lib = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir  = pkg_dir / ".lake" / "build" / "ir"
    base_lib_stem = rel.with_suffix("").name  # e.g. "Init"
    base_ir_stem = base_lib_stem
    for d, base in [(lib / rel.parent, base_lib_stem),
                    (ir  / rel.parent, base_ir_stem)]:
        if not d.exists():
            continue
        for f in d.iterdir():
            if f.name == base or f.name.startswith(base + "."):
                f.unlink()

    res = subprocess.run(
        ["lake", "build", module, "-v"],
        cwd=WORKSPACE, capture_output=True, text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(f"lake build {module} failed:\n{res.stdout}\n{res.stderr}")

    abs_src = str(src)
    for line in res.stdout.splitlines():
        if not line.startswith(TRACE_PREFIX):
            continue
        argv = line[len(TRACE_PREFIX):]
        if abs_src in argv:
            return argv
    raise RuntimeError(
        f"No trace: .> line for {module} in lake output. Captured "
        f"{sum(1 for l in res.stdout.splitlines() if l.startswith(TRACE_PREFIX))} "
        f"trace lines total."
    )


def _argv_from_trace(trace_argv: str) -> tuple[dict[str, str], list[str]]:
    """Parse a ``LEAN_PATH=... lean ...`` trace into (env, argv).

    Lake emits exactly one env var (LEAN_PATH) followed by the binary and args.
    No quoting or shell metacharacters appear in mathlib paths.
    """
    parts = trace_argv.split(" ")
    env: dict[str, str] = {}
    i = 0
    while i < len(parts) and "=" in parts[i] and not parts[i].startswith("/"):
        k, _, v = parts[i].partition("=")
        env[k] = v
        i += 1
    return env, parts[i:]


def validate_commands(module: str) -> int:
    """Run lake-build for the module and diff its argv against our extraction."""
    lean_bin = discover_lean_binary()
    packages = package_dirs()
    node = lean_module_node(module, lean_bin=lean_bin, packages=packages)

    trace = _capture_lake_trace_for_module(module)
    actual_env, actual_argv = _argv_from_trace(trace)

    expected_env = node.env
    expected_argv = node.command

    print(f"=== validate-commands: {module} ===")
    diffs: list[str] = []

    # env diff
    for k in sorted(set(expected_env) | set(actual_env)):
        e = expected_env.get(k); a = actual_env.get(k)
        if e != a:
            diffs.append(f"env[{k}]: expected={e!r} actual={a!r}")

    # argv diff
    if expected_argv != actual_argv:
        for i, (e, a) in enumerate(zip(expected_argv, actual_argv)):
            if e != a:
                diffs.append(f"argv[{i}]: expected={e!r} actual={a!r}")
        if len(expected_argv) != len(actual_argv):
            diffs.append(
                f"argv length: expected={len(expected_argv)} actual={len(actual_argv)}"
            )

    if diffs:
        print("MISMATCH:")
        for d in diffs:
            print(f"  {d}")
        return 1

    print("MATCH")
    return 0


# ---------------------------------------------------------------------------
# v1: module registry + static setup.json derivation
# ---------------------------------------------------------------------------

@dataclass
class ImportEdge:
    """One edge of the import graph, with the flags Lake uses for filtering."""
    module: str
    is_exported: bool
    is_meta: bool
    import_all: bool


@dataclass
class ModuleEntry:
    name: str
    src: Path
    pkg: str
    lib: str           # first segment of `name` — Lake convention for default roots
    is_module: bool    # from lean --deps-json
    imports: list[ImportEdge]  # imports with flags, deduped by (module, isMeta, importAll, isExported)


def _walk_lean_sources(packages: dict[str, Path]) -> list[tuple[str, Path]]:
    """Yield (pkg_name, abs_path) for every .lean source under each package.

    Skips `.lake/` (build/cache state) and `.git/` to keep the registry to
    actual sources.
    """
    out: list[tuple[str, Path]] = []
    for pkg_name, pkg_dir in packages.items():
        for root, dirs, files in os.walk(pkg_dir):
            # prune unwanted subtrees in-place
            dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
            for fname in files:
                if not fname.endswith(".lean"):
                    continue
                if fname == "lakefile.lean":
                    continue
                out.append((pkg_name, Path(root) / fname))
    return out


def _path_to_module(pkg_dir: Path, src: Path) -> str:
    """``<pkg_dir>/Foo/Bar/Baz.lean`` -> ``Foo.Bar.Baz``.

    Mathlib + every upstream lakefile we surveyed uses default roots
    (lib name = first path segment), so the path-to-module mapping is
    simply dotted segments under the package directory.
    """
    rel = src.relative_to(pkg_dir).with_suffix("")
    return ".".join(rel.parts)


def build_module_registry(packages: dict[str, Path]) -> dict[str, ModuleEntry]:
    """Walk all .lean files across packages and parse imports in one batch."""
    triples = _walk_lean_sources(packages)  # (pkg, abs_path)

    # Issue one lean --deps-json call over all paths (this is what
    # dag_traversal.py does for mathlib's own dirs; we extend the input set).
    stdin_data = "\n".join(str(p) for _, p in triples)
    res = subprocess.run(
        ["lake", "env", "lean", "--deps-json", "--stdin"],
        input=stdin_data, cwd=WORKSPACE,
        capture_output=True, text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(
            f"lean --deps-json failed (exit {res.returncode}):\n{res.stderr}"
        )
    data = json.loads(res.stdout)
    entries = data["imports"]
    if len(entries) != len(triples):
        raise RuntimeError(
            f"deps-json returned {len(entries)} entries for {len(triples)} files"
        )

    registry: dict[str, ModuleEntry] = {}
    collisions: dict[str, list[Path]] = {}
    for (pkg_name, abs_path), entry in zip(triples, entries):
        if entry.get("errors"):
            # Files that fail header parsing are recorded with empty imports.
            # dag_traversal does the same; this preserves DAG completeness for
            # files that aren't actually in the build graph.
            print(
                f"warning: deps-json: {abs_path}: {'; '.join(entry['errors'])}",
                file=sys.stderr,
            )
        result = entry.get("result") or {}
        is_module = bool(result.get("isModule", False))
        # Keep the raw deps-json edge list with flags. We do NOT collapse on
        # module-name alone because the same module can be imported twice
        # (typically once as runtime, once as meta) and Lake's traversal
        # treats them distinctly. We do collapse exact duplicates, though.
        imports: list[ImportEdge] = []
        seen_edges: set[tuple[str, bool, bool, bool]] = set()
        for imp in result.get("imports", []):
            edge = ImportEdge(
                module=imp["module"],
                is_exported=bool(imp.get("isExported", False)),
                is_meta=bool(imp.get("isMeta", False)),
                import_all=bool(imp.get("importAll", False)),
            )
            key = (edge.module, edge.is_exported, edge.is_meta, edge.import_all)
            if key in seen_edges:
                continue
            seen_edges.add(key)
            imports.append(edge)

        module_name = _path_to_module(packages[pkg_name], abs_path)
        if module_name in registry:
            collisions.setdefault(module_name, [registry[module_name].src]).append(
                abs_path
            )
            continue
        lib = module_name.split(".", 1)[0]
        registry[module_name] = ModuleEntry(
            name=module_name,
            src=abs_path,
            pkg=pkg_name,
            lib=lib,
            is_module=is_module,
            imports=imports,
        )

    if collisions:
        # Two .lean files mapping to the same module name — should never happen
        # in a clean Lake workspace; surface it loudly.
        msg = "; ".join(
            f"{m} -> {', '.join(str(p) for p in paths)}"
            for m, paths in collisions.items()
        )
        raise RuntimeError(f"module name collision in registry: {msg}")

    return registry


def transitive_imports(
    module: str, registry: dict[str, ModuleEntry],
) -> tuple[list[str], dict[str, bool]]:
    """All transitive imports of `module` that go into Lake's ``importArts``.

    Mirrors ``Lake.Build.Module.fetchTransImportArts`` (Lake/Build/Module.lean
    around line 222). The rule is:

      - Direct imports are always included (regardless of flags).
      - For transitive children, an edge ``parent -> child`` is followed only
        if ``parent_importAll || child.isExported``.
      - The new ``importAll`` carried into the child is
        ``nonModule || (parent_importAll && child.importAll)``. For
        module-style files (mathlib, every upstream we have) ``nonModule`` is
        false, so importAll only propagates through chains where every link
        is itself ``importAll``. For non-module-style importers (e.g. mathlib's
        ``Cache.*`` lib), ``nonModule = true`` collapses every visited entry
        to importAll=true, which means each importArts entry uses ``allArts``
        (4 paths instead of 3 for module-style imports).

      - A module first visited with importAll=false can be promoted to
        importAll=true on a later visit (Lake calls this the "size 3 -> 4"
        promotion). Stdlib/runtime modules (``Init``, ``Lean.*``) are not in
        the registry, so they're naturally excluded.

    Returns ``(ordered_module_names, importAll_per_module)``.
    """
    if module not in registry:
        raise KeyError(f"module {module!r} not in registry")

    entry = registry[module]
    non_module = not entry.is_module  # mathlib + upstream are all module-style

    # Track the strongest importAll seen for each module — a later visit with
    # importAll=True can promote an earlier importAll=False entry. For Mathlib
    # and current upstreams, importAll is rare; the promotion path mostly
    # doesn't fire, but we model it for correctness.
    seen_importAll: dict[str, bool] = {}
    ordered: list[str] = []

    # Seed: direct imports are always added; their children are enqueued via
    # the same rule used inside `walk` (importAll || child.isExported).
    queue: deque[tuple[str, bool]] = deque()
    for imp in entry.imports:
        if imp.module not in registry:
            continue
        # parent_importAll for the direct import = nonModule || imp.importAll
        # (so module-style: just imp.importAll).
        parent_importAll = non_module or imp.import_all
        if imp.module not in seen_importAll:
            seen_importAll[imp.module] = parent_importAll
            ordered.append(imp.module)
        elif parent_importAll and not seen_importAll[imp.module]:
            # promote
            seen_importAll[imp.module] = True
        # Enqueue *children* of this direct import using the parent_importAll.
        for child in registry[imp.module].imports:
            if child.module not in registry:
                continue
            if parent_importAll or child.is_exported:
                child_importAll = non_module or (parent_importAll and child.import_all)
                queue.append((child.module, child_importAll))

    while queue:
        m, importAll = queue.popleft()
        # Already known with at-least-equivalent importAll? Skip (matches Lake's
        # `if let some arts := s.find? mod.name` short-circuit, which also
        # handles the size==3 -> size==4 promotion case).
        existing = seen_importAll.get(m)
        if existing is not None and (existing or not importAll):
            continue
        seen_importAll[m] = importAll
        if existing is None:
            ordered.append(m)
        for child in registry[m].imports:
            if child.module not in registry:
                continue
            if importAll or child.is_exported:
                child_importAll = non_module or (importAll and child.import_all)
                queue.append((child.module, child_importAll))

    return ordered, seen_importAll


def module_artifact_paths(
    module: str,
    registry: dict[str, ModuleEntry],
    packages: dict[str, Path],
    *,
    import_all: bool,
) -> list[str]:
    """Return the artifact paths Lake records for `module` in ``importArts``.

    Layout depends on the imported module's style and the effective
    ``importAll`` of its visit (see Lake/Build/Module.lean:237 ``"size of 1 =
    non-module, 3 = module system import, 4 = import all"``):

      - non-module imported file: ``[olean]`` (1 path)
      - module-style + importAll=False: ``[olean, ir, olean.server]`` (3)
      - module-style + importAll=True : ``[olean, ir, olean.server,
        olean.private]`` (4)
    """
    entry = registry[module]
    pkg_dir = packages[entry.pkg]
    rel = module_to_relpath(module).with_suffix("")
    lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    olean = str(lib_dir / rel.with_suffix(".olean"))
    if not entry.is_module:
        return [olean]
    paths = [
        olean,
        str(lib_dir / rel.with_suffix(".ir")),
        str(lib_dir / rel.with_suffix(".olean.server")),
    ]
    if import_all:
        paths.append(str(lib_dir / rel.with_suffix(".olean.private")))
    return paths


@dataclass
class _LibOptionsCache:
    """Cache of (pkg, lib) -> options dict.

    Populated lazily: first time a module from a (pkg, lib) is encountered,
    we run ``lake setup-file`` on its source and cache the resulting options.
    Every subsequent module from the same lib reuses the cached value.
    """
    by_lib: dict[tuple[str, str], dict] = field(default_factory=dict)

    def options_for(self, entry: ModuleEntry) -> dict:
        key = (entry.pkg, entry.lib)
        if key not in self.by_lib:
            setup = lake_setup_file(entry.src)
            self.by_lib[key] = setup["options"]
        return self.by_lib[key]


def derive_setup_json(
    module: str,
    registry: dict[str, ModuleEntry],
    packages: dict[str, Path],
    lib_options: _LibOptionsCache,
) -> dict:
    """Construct a module's setup.json from registry + per-lib options.

    Plugins and dynlibs are empty per the §10.11 pre-flight (mathlib + every
    upstream we depend on stays in regime 1: no precompileModules, no plugins).
    If a future package introduces them, the validate-setup diff will trip.
    """
    entry = registry[module]
    options = lib_options.options_for(entry)
    deps, importAll_map = transitive_imports(module, registry)

    importArts: dict[str, list[str]] = {
        m: module_artifact_paths(
            m, registry, packages, import_all=importAll_map[m],
        )
        for m in deps
    }

    return {
        "name": lean_name_repr(module),
        "package": entry.pkg,
        "isModule": entry.is_module,
        "options": options,
        "plugins": [],
        "dynlibs": [],
        "importArts": importArts,
    }


# ---------------------------------------------------------------------------
# lean_exe configuration (mathlib's lakefile.lean)
#
# We mirror the static declarations rather than parsing the lakefile DSL —
# all eight exes are declared with literal fields, so a hand-written table
# matches the file 1:1 today and the validate-commands sub-command will trip
# if anyone edits the lakefile in a way that drifts from this table.
# ---------------------------------------------------------------------------

@dataclass
class LeanExeConfig:
    name: str          # exe name (e.g. "autolabel"), also the exe binary's name
    root: str          # root module name as Lake sees it (e.g. "autolabel" or "Cache.Main")
    src_dir: str       # srcDir under the package; "" if root maps to <pkg>/<root>.lean
    src_file: str      # path under the package, with extension (e.g. "scripts/autolabel.lean")
    support_interpreter: bool
    weak_link_args: list[str]


LEAN_EXES: dict[str, LeanExeConfig] = {
    "autolabel": LeanExeConfig(
        "autolabel", "autolabel", "scripts", "scripts/autolabel.lean",
        support_interpreter=False, weak_link_args=[],
    ),
    "cache": LeanExeConfig(
        "cache", "Cache.Main", "", "Cache/Main.lean",
        support_interpreter=False, weak_link_args=[],
    ),
    "check-yaml": LeanExeConfig(
        "check-yaml", "check-yaml", "scripts", "scripts/check-yaml.lean",
        support_interpreter=True, weak_link_args=[],
    ),
    "mk_all": LeanExeConfig(
        "mk_all", "mk_all", "scripts", "scripts/mk_all.lean",
        support_interpreter=True, weak_link_args=["-lLake"],
    ),
    "lint-style": LeanExeConfig(
        "lint-style", "lint-style", "scripts", "scripts/lint-style.lean",
        support_interpreter=True, weak_link_args=["-lLake"],
    ),
    "check_title_labels": LeanExeConfig(
        "check_title_labels", "check_title_labels", "scripts",
        "scripts/check_title_labels.lean",
        support_interpreter=False, weak_link_args=[],
    ),
    "nightly-testing-checklist": LeanExeConfig(
        "nightly-testing-checklist", "nightly-testing-checklist", "scripts",
        "scripts/nightly-testing-checklist.lean",
        support_interpreter=False, weak_link_args=[],
    ),
    "mathlib_test_executable": LeanExeConfig(
        "mathlib_test_executable", "MathlibTest.MathlibTestExecutable", "",
        "MathlibTest/MathlibTestExecutable.lean",
        support_interpreter=False, weak_link_args=[],
    ),
}


# Toolchain-static cc flags. Captured empirically from `lake build -v autolabel`
# (§5.3). All paths are relative to the toolchain root; the placeholder
# substitution turns them into absolute paths at execution time. validate-cc
# (planned) will diff these against a fresh capture to flag toolchain drift.
CC_COMPILE_FLAGS = [
    "-fstack-clash-protection",
    "-fdata-sections",
    "-ffunction-sections",
    "-fvisibility=hidden",
    "-Wno-unused-command-line-argument",
    "--sysroot", "$TOOLCHAIN_ROOT",
    "-nostdinc",
    "-isystem", "$TOOLCHAIN_ROOT/include/clang",
    "-O3",
    "-DNDEBUG",
]

# Static tail of the cc_link rsp. Same toolchain provenance as
# CC_COMPILE_FLAGS. Note that ``-lLake`` already appears here, so the
# weakLinkArgs=["-lLake"] declared on mk_all/lint-style produces a redundant
# (but harmless) double ``-lLake`` on those exes' rsps. We mirror Lake's
# behavior verbatim.
CC_LINK_RSP_TAIL = [
    "-L", "$TOOLCHAIN_ROOT/lib/lean",
    "--sysroot", "$TOOLCHAIN_ROOT",
    "-L", "$TOOLCHAIN_ROOT/lib",
    "-L", "$TOOLCHAIN_ROOT/lib/libc",
    "-fuse-ld=lld",
    "-lleancpp", "-lInit", "-lStd", "-lLean", "-lleanrt",
    "-lc++", "-lLake", "-lgmp", "-luv",
    "-Wl,-dead_strip",
]


# ---------------------------------------------------------------------------
# Raw transitive imports (Lake's recComputeTransImports — no isExported filter)
#
# Distinct from `transitive_imports` (which mirrors fetchTransImportArts and
# is used for setup.json importArts). Used for collecting object files at the
# link step, which needs every transitive import regardless of export flags.
# Order matches the OrdModuleSet insertion order Lake uses in
# collectImportsAux: post-order DFS, dedup preserving first occurrence.
# ---------------------------------------------------------------------------

def raw_transitive_imports(
    module: str, registry: dict[str, ModuleEntry],
) -> list[str]:
    """Return all transitive imports of `module` in Lake's link-time order."""
    if module not in registry:
        raise KeyError(module)
    cache: dict[str, list[str]] = {}

    def trans(mod: str) -> list[str]:
        if mod in cache:
            return cache[mod]
        if mod not in registry:
            cache[mod] = []
            return cache[mod]
        out: list[str] = []
        seen: set[str] = set()
        # Module-name dedup at the source: Lake's recParseImports collapses
        # multiple flag-distinct edges to the same module into a single Module
        # before walking, so we walk by unique module names.
        unique_imports: list[str] = []
        seen_imports: set[str] = set()
        for imp in registry[mod].imports:
            if imp.module in seen_imports:
                continue
            seen_imports.add(imp.module)
            unique_imports.append(imp.module)
        for d in unique_imports:
            for x in trans(d):
                if x not in seen:
                    seen.add(x)
                    out.append(x)
            if d in registry and d not in seen:
                seen.add(d)
                out.append(d)
        cache[mod] = out
        return out

    return trans(module)


# ---------------------------------------------------------------------------
# Path placeholders — relativize for portable graph emission, absolutize
# inside the executor at run time.
# ---------------------------------------------------------------------------

def _placeholder_ctx(lean_bin: Path) -> list[tuple[str, str]]:
    """Ordered prefix list for relativize/absolutize.

    Order is most-specific first so a path under ``$LAKE_HOME`` doesn't get
    matched as ``$WORKSPACE/.lake/...``. ``$TOOLCHAIN`` points at the bin
    directory; ``$TOOLCHAIN_ROOT`` at the toolchain sysroot — cc and link
    flags reference both ``<toolchain>/bin`` and ``<toolchain>/lib*``.
    """
    return [
        ("LAKE_HOME", str(LAKE_HOME)),
        ("WORKSPACE", str(WORKSPACE)),
        ("TOOLCHAIN", str(lean_bin.parent)),       # <root>/bin
        ("TOOLCHAIN_ROOT", str(lean_bin.parent.parent)),  # <root>
    ]


def relativize(s: str, ctx: list[tuple[str, str]]) -> str:
    for var, prefix in ctx:
        if s == prefix:
            return f"${var}"
        sep = "/"  # paths in the graph are POSIX-style
        if s.startswith(prefix + sep):
            return f"${var}{s[len(prefix):]}"
    return s


def absolutize(s: str, ctx: list[tuple[str, str]]) -> str:
    for var, value in ctx:
        token = f"${var}"
        if s == token:
            return value
        if s.startswith(token + "/"):
            return value + s[len(token):]
    return s


def _relativize_obj(obj, ctx: list[tuple[str, str]]):
    """Recursively relativize every string value in a JSON-ish structure.

    Handles the ``@<path>`` form used by ``cc -o foo @foo.rsp`` — strips the
    ``@`` prefix, relativizes the path part, re-adds ``@``.
    """
    if isinstance(obj, str):
        if obj.startswith("@"):
            return "@" + relativize(obj[1:], ctx)
        return relativize(obj, ctx)
    if isinstance(obj, list):
        return [_relativize_obj(x, ctx) for x in obj]
    if isinstance(obj, dict):
        return {k: _relativize_obj(v, ctx) for k, v in obj.items()}
    return obj


# ---------------------------------------------------------------------------
# Whole-graph emission
# ---------------------------------------------------------------------------

def _build_lean_module_node_dict(
    module: str,
    *,
    registry: dict[str, ModuleEntry],
    packages: dict[str, Path],
    lib_options: _LibOptionsCache,
    lean_bin: Path,
) -> dict:
    """Pure-dict node for a Lean module — what `emit-graph` writes per node.

    Paths are *absolute*. Relativization is a separate post-pass so the same
    builder serves both the graph-execution path (uses absolutes directly) and
    the JSON-emission path (rewrites to ``$WORKSPACE``/etc.).
    """
    entry = registry[module]
    pkg_dir = packages[entry.pkg]
    rel = module_to_relpath(module)

    lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir_dir = pkg_dir / ".lake" / "build" / "ir"
    olean = str(lib_dir / rel.with_suffix(".olean"))
    ilean = str(lib_dir / rel.with_suffix(".ilean"))
    c     = str(ir_dir  / rel.with_suffix(".c"))
    setup_path = str(ir_dir / rel.with_suffix(".setup.json"))

    setup_json = derive_setup_json(module, registry, packages, lib_options)

    command = [
        str(lean_bin),
        str(entry.src),
        "-o", olean,
        "-i", ilean,
        "-c", c,
        "--setup", setup_path,
        "--json",
    ]
    env = {"LEAN_PATH": lean_path_string(packages)}

    # `inputs` enumerates the files the worker needs in place before the
    # command runs: the source file, the to-be-written setup.json, and every
    # path mentioned in importArts. The setup.json file isn't an *input* in
    # the strict sense — the worker writes it from `setup_json` — but listing
    # it makes hermeticity explicit (it is what `lean --setup` reads).
    inputs: list[dict] = [{"path": str(entry.src), "kind": "source"}]
    inputs.append({"path": setup_path, "kind": "setup_json"})
    for art_module, paths in setup_json["importArts"].items():
        for p in paths:
            inputs.append({"path": p, "kind": "import_art", "module": art_module})

    # Outputs: everything Lake's compileLeanModule writes for this module.
    outputs = [
        olean,
        ilean,
        c,
    ]
    if entry.is_module:
        outputs.extend([
            str(lib_dir / rel.with_suffix(".olean.server")),
            str(lib_dir / rel.with_suffix(".olean.private")),
            str(lib_dir / rel.with_suffix(".ir")),
        ])
    outputs.append(setup_path)

    # Build-graph deps: every module whose oleans appear as importArts inputs.
    graph_deps = sorted(setup_json["importArts"].keys())

    return {
        "id": f"{entry.pkg}:{module}",
        "kind": "lean_module",
        "module": module,
        "package": entry.pkg,
        "command": command,
        "env": env,
        "inputs": inputs,
        "outputs": outputs,
        "setup_json": setup_json,
        "graph_deps": graph_deps,
    }


def _build_exe_lean_module_node(
    exe: LeanExeConfig,
    *,
    registry: dict[str, ModuleEntry],
    packages: dict[str, Path],
    lib_options: _LibOptionsCache,
    lean_bin: Path,
) -> dict:
    """Build the lean_module node that compiles the exe's root .lean file.

    Differs from a regular library module's node:
      * The Lake-side module name is ``exe.root`` (not the file's path-derived
        name). E.g. ``scripts/autolabel.lean`` → module ``autolabel``.
      * Outputs land at ``<pkg>/.lake/build/lib/lean/<root>.olean`` etc., not
        nested under the original directory of the source file.
      * Options come from the exe's owning lib, which for mathlib is none —
        the captured `lake setup-file` says ``options: {}``. We reflect that
        by *not* applying any per-lib options for these nodes.
      * isModule is read off the file's deps-json result.

    Transitive imports' artifact paths still come from the regular module
    registry (paths in their owning packages' build dirs), so the importArts
    structure is consistent.
    """
    # The exe's root .lean file. Its path-derived registry entry uses the
    # full dotted path (e.g. "scripts.autolabel"); we use that to read flags.
    src_abs = WORKSPACE / exe.src_file
    if not src_abs.exists():
        raise FileNotFoundError(f"lean_exe {exe.name} source not found: {src_abs}")

    # Find the registry entry (keyed by path-derived module name).
    file_module_name = _path_to_module(WORKSPACE, src_abs)
    if file_module_name not in registry:
        raise RuntimeError(
            f"lean_exe {exe.name}: source file not in registry as "
            f"{file_module_name!r} — registry-walk regression"
        )
    file_entry = registry[file_module_name]

    # Build a synthetic "exe view" of the entry that uses the Lake-side root
    # name. We don't mutate the registry (other code keys off the path-name).
    pkg_dir = packages["mathlib"]  # all mathlib lean_exes belong to mathlib
    rel = Path(*exe.root.split(".")).with_suffix(".olean").parent / (
        Path(*exe.root.split(".")).with_suffix(".olean").name
    )
    # Output paths use the exe.root dotted path -> file path mapping under
    # .lake/build/{lib/lean,ir}/<dots-as-slashes>.<ext>
    root_rel = Path(*exe.root.split("."))
    lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir_dir = pkg_dir / ".lake" / "build" / "ir"
    olean = str(lib_dir / root_rel.with_suffix(".olean"))
    ilean = str(lib_dir / root_rel.with_suffix(".ilean"))
    c     = str(ir_dir  / root_rel.with_suffix(".c"))
    setup_path = str(ir_dir / root_rel.with_suffix(".setup.json"))

    # Setup.json content: derive from the file's imports. Because the lean_exe
    # has no associated lean_lib, options come back empty (verified empirically
    # for autolabel: setup.json options == {}).
    deps, importAll_map = transitive_imports(file_module_name, registry)
    importArts = {
        m: module_artifact_paths(m, registry, packages, import_all=importAll_map[m])
        for m in deps
    }
    setup_json = {
        "name": lean_name_repr(exe.root),
        "package": file_entry.pkg,  # = "mathlib"
        "isModule": file_entry.is_module,
        "options": {},
        "plugins": [],
        "dynlibs": [],
        "importArts": importArts,
    }

    command = [
        str(lean_bin),
        str(src_abs),
        "-o", olean,
        "-i", ilean,
        "-c", c,
        "--setup", setup_path,
        "--json",
    ]
    env = {"LEAN_PATH": lean_path_string(packages)}

    inputs: list[dict] = [
        {"path": str(src_abs), "kind": "source"},
        {"path": setup_path, "kind": "setup_json"},
    ]
    for art_module, paths in importArts.items():
        for p in paths:
            inputs.append({"path": p, "kind": "import_art", "module": art_module})

    outputs = [olean, ilean, c]
    if file_entry.is_module:
        outputs.extend([
            str(lib_dir / root_rel.with_suffix(".olean.server")),
            str(lib_dir / root_rel.with_suffix(".olean.private")),
            str(lib_dir / root_rel.with_suffix(".ir")),
        ])
    outputs.append(setup_path)

    return {
        "id": f"mathlib:exe:{exe.name}:lean",
        "kind": "lean_module",
        "module": exe.root,
        "package": "mathlib",
        "command": command,
        "env": env,
        "inputs": inputs,
        "outputs": outputs,
        "setup_json": setup_json,
        "graph_deps": sorted(importArts.keys()),
    }


def _module_c_path(module: str, registry: dict[str, ModuleEntry],
                   packages: dict[str, Path]) -> str:
    """Absolute path to ``module``'s ``.c`` artifact."""
    entry = registry[module]
    pkg_dir = packages[entry.pkg]
    rel = module_to_relpath(module).with_suffix("")
    return str(pkg_dir / ".lake" / "build" / "ir" / rel.with_suffix(".c"))


def _module_c_o_export_path(module: str, registry: dict[str, ModuleEntry],
                             packages: dict[str, Path]) -> str:
    """Absolute path to ``module``'s ``.c.o.export`` artifact."""
    entry = registry[module]
    pkg_dir = packages[entry.pkg]
    rel = module_to_relpath(module).with_suffix("")
    return str(pkg_dir / ".lake" / "build" / "ir" / rel.with_suffix(".c.o.export"))


def _exe_root_c_path(exe: LeanExeConfig, packages: dict[str, Path]) -> str:
    pkg_dir = packages["mathlib"]
    root_rel = Path(*exe.root.split("."))
    return str(pkg_dir / ".lake" / "build" / "ir" / root_rel.with_suffix(".c"))


def _exe_root_c_o_export_path(exe: LeanExeConfig, packages: dict[str, Path]) -> str:
    pkg_dir = packages["mathlib"]
    root_rel = Path(*exe.root.split("."))
    return str(pkg_dir / ".lake" / "build" / "ir" / root_rel.with_suffix(".c.o.export"))


def _build_cc_compile_node(
    *,
    src_c_path: str,
    out_co_export_path: str,
    module_label: str,
    package: str,
    cc_bin: Path,
    toolchain_root: Path,
) -> dict:
    """Build the cc -c node that compiles a module's ``.c`` to ``.c.o.export``.

    The argv shape is:

        cc -c -o <out> <src> -I <toolchain>/include <CC_COMPILE_FLAGS> -DLEAN_EXPORTING

    No environment variables. CC_COMPILE_FLAGS uses the ``$TOOLCHAIN_ROOT``
    placeholder so the same node JSON is portable across machines.
    """
    cmd = [
        str(cc_bin),
        "-c",
        "-o", out_co_export_path,
        src_c_path,
        "-I", f"{toolchain_root}/include",
        *[arg.replace("$TOOLCHAIN_ROOT", str(toolchain_root)) for arg in CC_COMPILE_FLAGS],
        "-DLEAN_EXPORTING",
    ]
    return {
        "id": f"{package}:cc_compile:{module_label}",
        "kind": "cc_compile",
        "module": module_label,
        "package": package,
        "command": cmd,
        "env": {},
        "inputs": [{"path": src_c_path, "kind": "c_source"}],
        "outputs": [out_co_export_path],
        "graph_deps": [],  # filled in by caller (the lean_module that produced .c)
    }


def _build_cc_link_node(
    exe: LeanExeConfig,
    *,
    obj_paths: list[str],
    cc_bin: Path,
    toolchain_root: Path,
    packages: dict[str, Path],
) -> dict:
    """Build the cc -o node that links the exe.

    Lake produces the rsp file as a side effect of mkArgs; we do the same in
    the worker (so the rsp is an *output* of this node, not an input).
    """
    pkg_dir = packages["mathlib"]
    bin_dir = pkg_dir / ".lake" / "build" / "bin"
    bin_path = str(bin_dir / exe.name)
    rsp_path = str(bin_dir / f"{exe.name}.rsp")

    # rsp content order mirrors recBuildExe: objs ++ weakArgs ++ traceArgs ++
    # ["-L", leanLibDir] ++ ccLinkFlags. traceArgs (= linkArgs) is empty for
    # every mathlib exe.
    rsp_args = list(obj_paths) + list(exe.weak_link_args) + [
        arg.replace("$TOOLCHAIN_ROOT", str(toolchain_root))
        for arg in CC_LINK_RSP_TAIL
    ]

    cmd = [
        str(cc_bin),
        "-o", bin_path,
        f"@{rsp_path}",
    ]
    env = {"MACOSX_DEPLOYMENT_TARGET": "99.0"}

    inputs = [{"path": p, "kind": "obj"} for p in obj_paths]
    inputs.append({"path": rsp_path, "kind": "response_file"})

    return {
        "id": f"mathlib:cc_link:{exe.name}",
        "kind": "cc_link",
        "exe_name": exe.name,
        "package": "mathlib",
        "command": cmd,
        "env": env,
        "inputs": inputs,
        "outputs": [bin_path, rsp_path],
        "rsp_path": rsp_path,
        "rsp_args": rsp_args,
        "graph_deps": [],  # filled in by caller
    }


def _topo_order_modules(
    targets: Iterable[str],
    registry: dict[str, ModuleEntry],
) -> list[str]:
    """Topological order over `transitive_imports` build edges.

    Result puts leaves (no in-registry imports) first, roots last. The order
    among siblings is by module name to keep the emitted graph deterministic.
    """
    # Build closure
    closure: set[str] = set()
    queue = list(targets)
    while queue:
        m = queue.pop()
        if m in closure:
            continue
        if m not in registry:
            continue
        closure.add(m)
        deps, _ = transitive_imports(m, registry)
        queue.extend(d for d in deps if d not in closure)

    # Edges: m -> d for each d in transitive_imports(m), restricted to closure.
    deps_of: dict[str, list[str]] = {}
    indeg: dict[str, int] = {m: 0 for m in closure}
    for m in closure:
        deps, _ = transitive_imports(m, registry)
        ds = sorted(d for d in deps if d in closure)
        deps_of[m] = ds
    # indegree: count of modules whose deps include `m` — i.e. how many
    # modules in the closure are still waiting on `m`. We want to emit `m`
    # AFTER its deps, so we order leaves (no deps) first.
    out: list[str] = []
    pending_deps: dict[str, set[str]] = {m: set(deps_of[m]) for m in closure}
    ready: list[str] = sorted(m for m in closure if not pending_deps[m])
    # successors for fast unblocking
    successors: dict[str, list[str]] = {m: [] for m in closure}
    for m, ds in deps_of.items():
        for d in ds:
            successors[d].append(m)

    import heapq
    heap = list(ready)
    heapq.heapify(heap)
    while heap:
        m = heapq.heappop(heap)
        out.append(m)
        for s in successors[m]:
            pending_deps[s].discard(m)
            if not pending_deps[s]:
                heapq.heappush(heap, s)

    if len(out) != len(closure):
        leftover = sorted(closure - set(out))
        raise RuntimeError(
            f"topo order incomplete; cycle suspected. "
            f"{len(out)}/{len(closure)} ordered. "
            f"Examples remaining: {leftover[:5]}"
        )
    return out


def emit_graph(target: str, *, output_path: Optional[Path]) -> dict:
    """Emit the build subgraph for ``target``.

    Dispatch:
      * ``target`` is a key in ``LEAN_EXES`` → emit the exe graph: regular
        lean_module closure + the exe's lean_module + cc_compile per object +
        cc_link.
      * Otherwise → treat as a module name and emit just the lean_module
        subgraph (existing v1 behavior).
    """
    packages = package_dirs()
    registry = build_module_registry(packages)
    lib_options = _LibOptionsCache()
    lean_bin = discover_lean_binary()
    cc_bin = lean_bin.parent / "clang"
    toolchain_root = lean_bin.parent.parent

    nodes: list[dict] = []

    if target in LEAN_EXES:
        exe = LEAN_EXES[target]
        # 1. Regular lean_module closure for the exe's transitive imports.
        #    The closure uses *registry* module names — which for the exe's
        #    own root file is the path-derived name (e.g. `scripts.autolabel`),
        #    *not* the Lake-side root (e.g. `autolabel`). We exclude the
        #    file-name entry because the lean_exe builds the source under a
        #    *different* output path; we'll add a dedicated exe-lean node next.
        file_module_name = _path_to_module(WORKSPACE, WORKSPACE / exe.src_file)

        # The exe's setup.json importArts gives us the *user* modules whose
        # oleans the lean compile reads. For closure-of-build, we need raw
        # transImports (no isExported filter) so cc_link can pick up every
        # module's .c.o.export.
        raw_deps = raw_transitive_imports(file_module_name, registry)

        # lean_module nodes for every transitive import (in topo order).
        for m in _topo_order_modules(raw_deps, registry):
            nodes.append(_build_lean_module_node_dict(
                m, registry=registry, packages=packages,
                lib_options=lib_options, lean_bin=lean_bin,
            ))

        # 2. lean_module node for the exe's own root.
        exe_lean_node = _build_exe_lean_module_node(
            exe, registry=registry, packages=packages,
            lib_options=lib_options, lean_bin=lean_bin,
        )
        nodes.append(exe_lean_node)

        # 3. cc_compile nodes — one per module whose .c is going into the
        #    link. Order = exe.root first, then raw_deps (matching Lake's
        #    objJobs accumulation order in recBuildExe).
        cc_nodes_by_module: dict[str, dict] = {}
        # exe root cc_compile
        cc_root = _build_cc_compile_node(
            src_c_path=_exe_root_c_path(exe, packages),
            out_co_export_path=_exe_root_c_o_export_path(exe, packages),
            module_label=exe.root,
            package="mathlib",
            cc_bin=cc_bin,
            toolchain_root=toolchain_root,
        )
        cc_root["graph_deps"] = [exe_lean_node["id"]]
        nodes.append(cc_root)
        cc_nodes_by_module[exe.root] = cc_root

        for m in raw_deps:
            entry = registry[m]
            cc = _build_cc_compile_node(
                src_c_path=_module_c_path(m, registry, packages),
                out_co_export_path=_module_c_o_export_path(m, registry, packages),
                module_label=m,
                package=entry.pkg,
                cc_bin=cc_bin,
                toolchain_root=toolchain_root,
            )
            # cc_compile depends on the module's lean_module having produced .c
            cc["graph_deps"] = [f"{entry.pkg}:{m}"]
            nodes.append(cc)
            cc_nodes_by_module[m] = cc

        # 4. cc_link node.
        link_objs: list[str] = [_exe_root_c_o_export_path(exe, packages)]
        for m in raw_deps:
            link_objs.append(_module_c_o_export_path(m, registry, packages))
        link_node = _build_cc_link_node(
            exe, obj_paths=link_objs, cc_bin=cc_bin,
            toolchain_root=toolchain_root, packages=packages,
        )
        link_node["graph_deps"] = [n["id"] for n in cc_nodes_by_module.values()]
        nodes.append(link_node)
    else:
        # Module-only target.
        if target not in registry:
            raise KeyError(f"target {target!r} not in registry")
        ordered = _topo_order_modules([target], registry)
        nodes = [
            _build_lean_module_node_dict(
                m, registry=registry, packages=packages,
                lib_options=lib_options, lean_bin=lean_bin,
            )
            for m in ordered
        ]

    ctx = _placeholder_ctx(lean_bin)
    nodes_rel = [_relativize_obj(n, ctx) for n in nodes]
    graph = {
        "version": "v1",
        "target": target,
        "workspace": {
            "WORKSPACE": str(WORKSPACE),
            "LAKE_HOME": str(LAKE_HOME),
            "TOOLCHAIN": str(lean_bin.parent),
            "TOOLCHAIN_ROOT": str(toolchain_root),
        },
        "node_count": len(nodes_rel),
        "nodes": nodes_rel,
    }

    if output_path is not None:
        output_path.write_text(json.dumps(graph, indent=1))
    return graph


# ---------------------------------------------------------------------------
# Pre-flight (§10.11): refuse to emit a graph from an unsupported workspace
# ---------------------------------------------------------------------------

# Lakefile constructs that would push the workspace out of regime 1 (the
# only regime where static graph extraction is sound). We grep for these
# across mathlib's lakefile *and* every active package's lakefile.
_DYNAMIC_FEATURES = ("target", "module_facet", "library_facet",
                     "extern_lib", "precompileModules")

# proofwidgets ships JS via dynamic targets — the analysis doc explicitly
# carves it out as an opaque `package_extra_dep` node, so its targets are
# expected and don't disqualify the workspace.
_KNOWN_DYNAMIC_PACKAGES = {"proofwidgets"}


def _grep_dynamic_features() -> list[tuple[str, int, str]]:
    """Find lakefile lines that declare a dynamic feature.

    Returns a list of (path, line_number, line_text). Excludes:
      * declarations under known-opaque packages (proofwidgets).
      * the literal ``precompileModules = false`` line aesop uses to
        explicitly *opt out* — keyword present, behavior off.
    """
    pattern = re.compile(
        r"^\s*("
        + "|".join(re.escape(f) for f in _DYNAMIC_FEATURES)
        + r")\b"
    )
    candidates: list[Path] = [WORKSPACE / "lakefile.lean"]
    if PACKAGES_DIR.exists():
        for pkg_dir in sorted(PACKAGES_DIR.iterdir()):
            if not pkg_dir.is_dir() or pkg_dir.name in _KNOWN_DYNAMIC_PACKAGES:
                continue
            for fname in ("lakefile.lean", "lakefile.toml"):
                p = pkg_dir / fname
                if p.exists():
                    candidates.append(p)

    hits: list[tuple[str, int, str]] = []
    for path in candidates:
        for i, line in enumerate(path.read_text().splitlines(), 1):
            m = pattern.search(line)
            if not m:
                continue
            # Filter `precompileModules = false` — boolean off is fine.
            if m.group(1) == "precompileModules" and re.search(r"=\s*false\b", line):
                continue
            hits.append((str(path), i, line.rstrip()))
    return hits


def preflight() -> int:
    """Run the §10.11 health check; report and return non-zero on any failure."""
    print("=== preflight: §10.11 health check ===")
    print()
    failed = False

    # 1. lake binary version vs lean-toolchain.
    res = subprocess.run(
        ["lake", "--version"], cwd=WORKSPACE,
        capture_output=True, text=True, check=True,
    )
    lake_version_line = res.stdout.strip()
    print(f"[lake] {lake_version_line}")
    toolchain_text = (WORKSPACE / "lean-toolchain").read_text().strip()
    print(f"[toolchain pin] {toolchain_text}")
    # Extract `Lean version 4.X.Y...` and compare against toolchain.
    m = re.search(r"Lean version (\S+?)\)", lake_version_line)
    if m:
        lake_lean_version = m.group(1)
        # toolchain pin is like "leanprover/lean4:v4.30.0-rc2"; strip prefix
        pin_version = toolchain_text.split(":")[-1].lstrip("v")
        if lake_lean_version != pin_version:
            print(f"  ! mismatch: lake reports {lake_lean_version!r} but "
                  f"lean-toolchain pins {pin_version!r}")
            failed = True
    print()

    # 2. dynamic feature scan.
    print("[dynamic feature scan]")
    hits = _grep_dynamic_features()
    if hits:
        print(f"  ! {len(hits)} unexpected dynamic-feature declaration(s):")
        for p, ln, text in hits[:20]:
            print(f"    {p}:{ln}: {text}")
        if len(hits) > 20:
            print(f"    ... and {len(hits) - 20} more")
        failed = True
    else:
        print("  OK — no `target`/`module_facet`/`library_facet`/`extern_lib`"
              " outside proofwidgets, no enabled `precompileModules`.")
    print()

    # 3. plugins/dynlibs spot check via setup-file.
    #    One sample per mathlib lean_lib + each upstream package.
    print("[plugins/dynlibs spot check (one module per lib)]")
    samples: list[tuple[str, Path]] = [
        ("Mathlib", WORKSPACE / "Mathlib" / "Init.lean"),
        ("Cache", WORKSPACE / "Cache" / "Hashing.lean"),
        ("Archive", WORKSPACE / "Archive.lean"),
        ("Counterexamples", WORKSPACE / "Counterexamples.lean"),
    ]
    # Use lake-manifest's authoritative package set, not raw .lake/packages/
    # iterdir (which includes stale dirs like `lean4-cli`).
    active_packages = package_dirs()
    for pkg_name, child in sorted(active_packages.items()):
        if pkg_name == "mathlib":
            continue
        # Prefer a deep file (a typical lib module) over top-level test
        # entrypoints — some packages have test "root" files that
        # `lake setup-file` doesn't accept.
        sample = None
        for f in sorted(child.rglob("*.lean")):
            rel_parts = f.relative_to(child).parts
            if ".lake" in rel_parts or rel_parts[-1] == "lakefile.lean":
                continue
            if len(rel_parts) < 2:
                # Top-level files like `LeanSearchClientTest.lean` aren't
                # always sample-able; prefer a nested file when available.
                continue
            sample = f
            break
        if sample is None:
            # Fall back to a top-level non-lakefile if no nested file exists.
            for f in sorted(child.rglob("*.lean")):
                rel_parts = f.relative_to(child).parts
                if ".lake" in rel_parts or rel_parts[-1] == "lakefile.lean":
                    continue
                sample = f
                break
        if sample is not None:
            samples.append((pkg_name, sample))
    for label, src in samples:
        if not src.exists():
            print(f"  - {label:20s} SKIP (no sample file at {src})")
            continue
        try:
            setup = lake_setup_file(src)
        except subprocess.CalledProcessError:
            print(f"  - {label:20s} ERROR running setup-file on {src}")
            failed = True
            continue
        plugins = setup.get("plugins", [])
        dynlibs = setup.get("dynlibs", [])
        ok = not plugins and not dynlibs
        marker = "OK" if ok else "FAIL"
        print(f"  - {label:20s} {marker}  plugins={len(plugins)} dynlibs={len(dynlibs)}")
        if not ok:
            failed = True

    print()
    if failed:
        print("PREFLIGHT FAILED — workspace is NOT in regime 1. Static graph "
              "extraction is unsound; fall back to instrumentation (§9).")
        return 1
    print("PREFLIGHT OK — static graph extraction is sound.")
    return 0


# ---------------------------------------------------------------------------
# Validation: end-to-end output equivalence (§7.2 of the analysis doc)
# ---------------------------------------------------------------------------

def _file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# Files we exclude from the diff:
#   - `.hash` / `.trace` / `.trace.nobuild` / `.rsp`: Lake-only sidecars whose
#     hashing scheme the reference executor doesn't replicate (§7.2).
#   - `.setup.json`: byte representation depends on JSON key/list emission
#     order, which Lake's `Lean.Json` and our Python emitter do differently.
#     Semantic equivalence is established separately by `validate-setup`,
#     and `lean --setup` reads it semantically so downstream artifacts
#     (.olean etc.) reproduce byte-exactly regardless.
_OUTPUT_EXCLUDE_SUFFIXES = (
    ".hash", ".trace", ".trace.nobuild", ".rsp", ".setup.json",
)


def _is_diffable_output(path: str) -> bool:
    return not any(path.endswith(s) for s in _OUTPUT_EXCLUDE_SUFFIXES)


def _delete_module_artifacts(parent: Path, stem: str) -> int:
    """Delete every regular file in `parent` whose name is `stem` or `stem.X`.

    Skips directories — a sibling subdirectory can share the stem (e.g. a
    `Lint/` subdir next to a `Lint.olean` for the lib's namespace module).
    Returns the count of files removed.
    """
    if not parent.exists():
        return 0
    n = 0
    for f in parent.iterdir():
        if not f.is_file():
            continue
        if f.name == stem or f.name.startswith(stem + "."):
            f.unlink()
            n += 1
    return n


def validate_outputs(target: str, *, full: bool = False) -> int:
    """End-to-end byte-equivalence check.

    Two modes:

      * **default (single-target)**: delete only the *target* node's outputs,
        rebuild the target alone via ``run_graph.py --only``, diff against the
        pre-existing golden hashes. Transitive deps are assumed already on
        disk (i.e. populated by Lake / ``lake exe cache get``). This is the
        cheap form usable per-PR / per-CI sample.
      * **full** (``--full``): delete every node's outputs, rebuild the whole
        closure via ``run_graph.py``, diff. Expensive — comparable to a
        ``lake build`` from clean. Only relevant for nightly-cadence checks.

    Sidecar files (``*.hash``, ``*.trace``, ``*.rsp``) are excluded from the
    diff per §7.2 — Lake writes them with its own hashing scheme that the
    reference executor doesn't replicate.

    The §7.2 spec form (``rm -rf .lake/build; lake build --no-cache``)
    establishes its baseline by *running Lake fresh*. We trust the existing
    cache as a stand-in: reproducibility was independently verified (a
    forced rebuild of a cached olean produced a byte-identical file).
    """
    packages = package_dirs()
    registry = build_module_registry(packages)
    is_exe = target in LEAN_EXES
    if not is_exe and target not in registry:
        raise KeyError(f"target {target!r} not in registry or LEAN_EXES")

    graph_path = Path(tempfile.mkstemp(prefix="build_graph_", suffix=".json")[1])
    try:
        emit_graph(target, output_path=graph_path)
        graph = json.loads(graph_path.read_text())
        ws = graph["workspace"]
        ctx = [
            ("LAKE_HOME", ws["LAKE_HOME"]),
            ("WORKSPACE", ws["WORKSPACE"]),
            ("TOOLCHAIN", ws["TOOLCHAIN"]),
            ("TOOLCHAIN_ROOT", ws.get("TOOLCHAIN_ROOT", str(Path(ws["TOOLCHAIN"]).parent))),
        ]

        if full:
            nodes_to_check = list(graph["nodes"])
        elif is_exe:
            exe_cfg = LEAN_EXES[target]
            nodes_to_check = [
                n for n in graph["nodes"]
                if (n.get("kind") == "cc_link" and n.get("exe_name") == target)
                or (n.get("kind") == "cc_compile" and n.get("module") == exe_cfg.root)
                or (n.get("kind") == "lean_module" and n.get("module") == exe_cfg.root)
            ]
        else:
            nodes_to_check = [n for n in graph["nodes"] if n.get("module") == target]

        outputs_abs: list[Path] = []
        for n in nodes_to_check:
            for o in n["outputs"]:
                if _is_diffable_output(o):
                    outputs_abs.append(Path(absolutize(o, ctx)))

        golden: dict[Path, str] = {}
        missing_pre: list[Path] = []
        for p in outputs_abs:
            if p.exists():
                golden[p] = _file_sha256(p)
            else:
                missing_pre.append(p)

        mode = "full" if full else "single-target"
        print(f"=== validate-outputs ({mode}): {target} ===")
        print(f"graph nodes: {graph['node_count']}  "
              f"checked nodes: {len(nodes_to_check)}  "
              f"diffable outputs: {len(outputs_abs)}  "
              f"golden present: {len(golden)}  "
              f"missing pre-run: {len(missing_pre)}")

        # Delete outputs to force a fresh rebuild. We delete by parent dir +
        # module stem so sidecars (.hash, .trace) also go.
        deleted = 0
        deleted_parents: set[tuple[Path, str]] = set()
        for p in outputs_abs:
            stem = p.name.split(".", 1)[0]
            key = (p.parent, stem)
            if key in deleted_parents:
                continue
            deleted_parents.add(key)
            deleted += _delete_module_artifacts(p.parent, stem)
        print(f"deleted {deleted} files (output set + sidecars)")

        # Run.
        run_graph_path = Path(__file__).parent / "run_graph.py"
        run_args = [sys.executable, str(run_graph_path), str(graph_path)]
        if full:
            pass  # run all nodes
        elif is_exe:
            # exe single-target: only the lean_module + cc_compile + cc_link
            # for the exe itself need rebuilding; transitive deps are golden.
            run_args.append("--missing")
        else:
            run_args.append("--only")
        res = subprocess.run(run_args, capture_output=True, text=True)
        if res.returncode != 0:
            sys.stderr.write(res.stdout)
            sys.stderr.write(res.stderr)
            print("run_graph.py FAILED")
            return res.returncode
        executed = len(graph["nodes"]) if full else 1
        print(f"run_graph.py: ok ({executed} nodes executed)")

        # Compare.
        missing_post: list[Path] = []
        diffs: list[str] = []
        for p in outputs_abs:
            if not p.exists():
                missing_post.append(p)
                continue
            old_hash = golden.get(p)
            if old_hash is None:
                continue
            new_hash = _file_sha256(p)
            if new_hash != old_hash:
                diffs.append(f"  {p}\n    golden  ={old_hash}\n    rebuilt ={new_hash}")

        if missing_post:
            print(f"MISSING after run ({len(missing_post)}):")
            for p in missing_post[:5]:
                print(f"  {p}")
            if len(missing_post) > 5:
                print(f"  ... and {len(missing_post) - 5} more")
        if diffs:
            print(f"BYTE DIFFS ({len(diffs)}):")
            for d in diffs[:5]:
                print(d)
            if len(diffs) > 5:
                print(f"  ... and {len(diffs) - 5} more")

        if missing_post or diffs:
            return 1
        print("ALL OUTPUTS MATCH GOLDEN")
        return 0
    finally:
        try:
            graph_path.unlink()
        except FileNotFoundError:
            pass


# ---------------------------------------------------------------------------
# Validation: derived setup.json vs oracle
# ---------------------------------------------------------------------------

def _canonicalize(d: object) -> str:
    """Stable JSON dump for semantic equality: sorted keys, no whitespace."""
    return json.dumps(d, sort_keys=True, separators=(",", ":"))


def validate_setup(module: str) -> int:
    """Diff the statically derived setup.json against ``lake setup-file``.

    Reports semantic equality (sort_keys) and, separately, whether Lake's
    *byte* representation of importArts/options ordering matches.
    """
    packages = package_dirs()
    registry = build_module_registry(packages)
    lib_cache = _LibOptionsCache()

    derived = derive_setup_json(module, registry, packages, lib_cache)
    oracle = lake_setup_file(registry[module].src)

    print(f"=== validate-setup: {module} ===")
    print(f"derived importArts count: {len(derived['importArts'])}")
    print(f"oracle  importArts count: {len(oracle['importArts'])}")

    semantic_ok = _canonicalize(derived) == _canonicalize(oracle)
    if semantic_ok:
        print("SEMANTIC: MATCH")
    else:
        print("SEMANTIC: MISMATCH")
        # Field-by-field diff to make the cause obvious.
        for k in sorted(set(derived) | set(oracle)):
            d = derived.get(k); o = oracle.get(k)
            if k == "importArts" and isinstance(d, dict) and isinstance(o, dict):
                only_derived = set(d) - set(o)
                only_oracle = set(o) - set(d)
                if only_derived:
                    print(f"  importArts only in derived ({len(only_derived)}): "
                          f"{sorted(only_derived)[:5]}{' ...' if len(only_derived) > 5 else ''}")
                if only_oracle:
                    print(f"  importArts only in oracle  ({len(only_oracle)}): "
                          f"{sorted(only_oracle)[:5]}{' ...' if len(only_oracle) > 5 else ''}")
                # path-content disagreement on shared keys
                shared = set(d) & set(o)
                bad_paths = [m for m in shared if d[m] != o[m]]
                if bad_paths:
                    sample = bad_paths[0]
                    print(f"  importArts path mismatch on {len(bad_paths)} entries; "
                          f"e.g. {sample}: derived={d[sample]} oracle={o[sample]}")
            elif d != o:
                print(f"  field {k!r}: derived={d!r} oracle={o!r}")
        return 1

    # If semantic OK, still report whether byte-equality holds (the strong
    # form Lake would write). Useful info; not failure.
    derived_bytes = json.dumps(derived, indent=1).encode()
    oracle_bytes = json.dumps(oracle, indent=1).encode()
    if derived_bytes == oracle_bytes:
        print("BYTE: MATCH")
    else:
        print(f"BYTE: differs (derived={len(derived_bytes)}B, oracle={len(oracle_bytes)}B) "
              f"— semantic equivalence still holds; key/list ordering differs.")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="lake_graph_extract")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_emit = sub.add_parser("emit", help="emit a single-module node JSON to stdout")
    p_emit.add_argument("module")

    p_val = sub.add_parser(
        "validate-commands",
        help="run lake build -v on a module and diff against the extracted command",
    )
    p_val.add_argument("module")

    p_setup = sub.add_parser(
        "validate-setup",
        help="diff statically-derived setup.json against `lake setup-file` output",
    )
    p_setup.add_argument("module")

    p_emit_graph = sub.add_parser(
        "emit-graph",
        help="emit the full lean_module subgraph for a target's transitive closure",
    )
    p_emit_graph.add_argument("target")
    p_emit_graph.add_argument("-o", "--output", type=Path, default=None,
                              help="output path (default: stdout)")

    sub.add_parser(
        "preflight",
        help="run the §10.11 health check; exit non-zero if the workspace "
             "isn't in regime 1",
    )

    p_val_out = sub.add_parser(
        "validate-outputs",
        help="end-to-end byte-equivalence check: delete the target's outputs, "
             "run the extracted graph, diff against golden hashes",
    )
    p_val_out.add_argument("target")
    p_val_out.add_argument(
        "--full", action="store_true",
        help="delete & rebuild the whole closure (slow); default is single-target",
    )

    args = parser.parse_args(argv)

    if args.cmd == "emit":
        lean_bin = discover_lean_binary()
        packages = package_dirs()
        node = lean_module_node(args.module, lean_bin=lean_bin, packages=packages)
        json.dump(
            {
                "id": node.id,
                "kind": node.kind,
                "command": node.command,
                "env": node.env,
                "inputs_count": len(node.inputs),
                "outputs": node.outputs,
                "setup_json_keys": sorted(node.setup_json.keys()),
            },
            sys.stdout, indent=2,
        )
        sys.stdout.write("\n")
        return 0

    if args.cmd == "validate-commands":
        return validate_commands(args.module)

    if args.cmd == "validate-setup":
        return validate_setup(args.module)

    if args.cmd == "emit-graph":
        graph = emit_graph(args.target, output_path=args.output)
        if args.output is None:
            json.dump(graph, sys.stdout, indent=1)
            sys.stdout.write("\n")
        else:
            print(f"wrote {args.output} ({graph['node_count']} nodes)")
        return 0

    if args.cmd == "validate-outputs":
        return validate_outputs(args.target, full=args.full)

    if args.cmd == "preflight":
        return preflight()

    parser.error(f"unknown subcommand: {args.cmd}")
    return 2


if __name__ == "__main__":
    sys.exit(main())
