#!/usr/bin/env python3
"""
Reusable parallel DAG traversal for Lean import graphs.

Parses the import DAG from `.lean` source files and parallelizes an action
over a forward or backward traversal.  Each module is submitted to the
thread pool the moment its last in-DAG dependency finishes, giving true
maximum parallelism.

CLI usage:
    dag_traversal.py --forward 'lake build {}'
    dag_traversal.py --forward -j4 'echo {}'

By default, {} is replaced with the file path (e.g. Mathlib/Foo/Bar.lean).
Use --module to substitute the module name instead (e.g. Mathlib.Foo.Bar):

    dag_traversal.py --backward --module 'my_script {}'

Library usage:
    from dag_traversal import DAG, DAGTraverser

    dag = DAG.from_directories(Path("."))
    traverser = DAGTraverser()
    results = traverser.traverse(dag, my_action, direction="backward")
"""

import argparse
import atexit
import heapq
import json
import os
import shlex
import signal
import subprocess
import sys
import time
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from threading import Event, Lock
from typing import Callable

# ANSI escape codes
CLEAR_LINE = "\033[2K"
HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"


class ShutdownError(Exception):
    """Raised when a shutdown has been requested (e.g. Ctrl-C)."""


class DAGTraverser:
    """Per-session state for parallel DAG traversal.

    Encapsulates shutdown coordination, in-flight file tracking, and
    active build management so that independent traversals don't share
    locks or state.
    """

    def __init__(self):
        #: Set on KeyboardInterrupt.  Action callbacks can check this
        #: to bail out early instead of spawning new subprocesses.
        self.shutdown_event = Event()

        # Thread-safe registry of in-flight file modifications.
        # On abnormal exit (e.g. Ctrl-C), files get reverted.
        self._inflight_lock = Lock()
        self._inflight: dict[Path, str] = {}  # filepath -> original content

        # Active lake build subprocesses, tracked so force_exit can kill them.
        self._active_builds_lock = Lock()
        self._active_builds: set[subprocess.Popen] = set()

        atexit.register(self._revert_inflight)

    def inflight_register(self, path: Path, content: str):
        """Register original file content so it can be reverted on abnormal exit."""
        with self._inflight_lock:
            self._inflight[path] = content

    def inflight_unregister(self, path: Path):
        """Unregister a file after processing completes normally."""
        with self._inflight_lock:
            self._inflight.pop(path, None)

    def _revert_inflight(self):
        with self._inflight_lock:
            for path, content in self._inflight.items():
                try:
                    path.write_text(content)
                except Exception:
                    pass
            self._inflight.clear()

    def _kill_builds(self):
        """Kill all active lake build process groups."""
        with self._active_builds_lock:
            for proc in self._active_builds:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    try:
                        proc.kill()
                    except ProcessLookupError:
                        pass

    def force_exit(self, code: int = 1):
        """Kill active builds, revert in-flight files, and force-exit.

        Uses os._exit to bypass ThreadPoolExecutor's atexit handler, which
        would block joining worker threads that may still be running builds.
        """
        self._kill_builds()
        self._revert_inflight()
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(code)

    def lake_build(
        self, module_name: str, project_dir: Path, timeout: int = 600,
    ) -> tuple[bool, str]:
        """Run lake build for a module. Returns (success, output).

        Checks shutdown_event before spawning and polls it every 0.5s during
        the build, killing the subprocess and raising ShutdownError if set.
        Each build runs in its own process group (start_new_session) so the
        entire tree (lake + lean children) can be killed cleanly.
        """
        if self.shutdown_event.is_set():
            raise ShutdownError("shutdown requested")
        proc = subprocess.Popen(
            ["lake", "build", module_name],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=project_dir,
            start_new_session=True,
        )
        with self._active_builds_lock:
            self._active_builds.add(proc)
        try:
            deadline = time.monotonic() + timeout
            # We poll communicate() with a short timeout instead of using
            # subprocess.run(timeout=...) so we can check shutdown_event
            # between iterations — this lets Ctrl-C abort promptly even
            # during long builds.
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    return False, "Build timed out"
                try:
                    stdout, _ = proc.communicate(timeout=min(remaining, 0.5))
                    return proc.returncode == 0, stdout
                except subprocess.TimeoutExpired:
                    if self.shutdown_event.is_set():
                        raise ShutdownError("shutdown requested")
        finally:
            with self._active_builds_lock:
                self._active_builds.discard(proc)
            if proc.poll() is None:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    proc.kill()
                proc.wait()

    def traverse(
        self,
        dag: "DAG",
        action: Callable[[str, Path], object],
        direction: str = "backward",
        max_workers: int | None = None,
        module_callback: Callable[[str, object, Exception | None], None] | None = None,
        progress_callback: Callable[[int, int, int], None] | None = None,
        stop_on_failure: bool = False,
        skip: set[str] | None = None,
        weights: dict[str, int] | None = None,
    ) -> list["TraversalResult"]:
        """Process modules in DAG order with maximum parallelism.

        When more modules are ready than workers available, modules with
        longer successor chains are scheduled first (critical-path
        priority), ensuring that work which unblocks the most future
        parallelism runs earliest.

        Args:
            dag: The DAG to traverse.
            action: Callable(module_name, filepath) -> result.  Raise to signal
                    failure.
            direction: "backward" (downstream first) or "forward" (upstream first).
            max_workers: Thread pool size (default: cpu_count).
            module_callback: Called after each module as (module_name, result, error).
            progress_callback: Called after each module as (completed, total, inflight).
            stop_on_failure: If True, when a module fails (action raises), its
                             successors in the DAG are skipped.
            skip: Set of module names to mark as completed without running the
                  action.  Useful after an initial build (e.g. a full ``lake build``)
                  identifies which modules are already clean.
            weights: Optional per-module weights for critical-path priority.
                     Modules not in the dict default to weight 0 (e.g. skip-set
                     modules).  When None, uniform weight 1 is used.

        Returns:
            List of TraversalResult for all processed modules.
        """
        all_names = set(dag.modules.keys())

        if direction == "backward":
            # Process modules that nothing depends on first.
            # A module's "dependencies" are its importers (things that import it);
            # once all importers are done, this module can run.
            deps_of = {
                name: [m for m in info.importers if m in all_names]
                for name, info in dag.modules.items()
            }
            successors_of = {
                name: [m for m in info.imports if m in all_names]
                for name, info in dag.modules.items()
            }
        elif direction == "forward":
            # Process modules with no imports first.
            deps_of = {
                name: [m for m in info.imports if m in all_names]
                for name, info in dag.modules.items()
            }
            successors_of = {
                name: [m for m in info.importers if m in all_names]
                for name, info in dag.modules.items()
            }
        else:
            raise ValueError(f"Unknown direction: {direction!r}")

        if max_workers is None:
            max_workers = os.cpu_count() or 4

        total = len(dag.modules)
        if total == 0:
            return []

        # Pre-compute critical-path depths so we can prioritise modules
        # that unblock the costliest chains of future work.
        depths = _compute_depths(successors_of, weights)

        lock = Lock()
        done_event = Event()
        remaining_deps: dict[str, int] = {
            name: len(deps_of[name]) for name in dag.modules
        }
        all_results: list[TraversalResult] = []
        completed_count = 0
        inflight = 0
        skipped: set[str] = set()

        # Priority queue of ready modules: (-depth, name).  Negative depth
        # gives us a max-heap so deeper chains are scheduled first.
        ready_queue: list[tuple[int, str]] = []

        def resolve(rel: Path) -> Path:
            if dag.project_root:
                return dag.project_root / rel
            return rel

        def mark_skipped(name: str):
            """Iteratively mark a module and all its successors as skipped."""
            stack = [name]
            while stack:
                n = stack.pop()
                if n in skipped:
                    continue
                skipped.add(n)
                for succ in successors_of.get(n, []):
                    if succ in remaining_deps and succ not in skipped:
                        stack.append(succ)

        def _drain_ready() -> list[str]:
            """Pop modules from the priority queue up to available workers.

            Must be called with *lock* held.  Returns the names to submit
            (submission itself happens outside the lock).
            """
            nonlocal inflight
            to_submit: list[str] = []
            while ready_queue and inflight < max_workers:
                _, name = heapq.heappop(ready_queue)
                inflight += 1
                to_submit.append(name)
            return to_submit

        def _do_submit(name: str):
            nonlocal inflight
            info = dag.modules[name]
            try:
                fut = executor.submit(action, name, resolve(info.filepath))
            except RuntimeError:
                # Executor shut down (e.g. KeyboardInterrupt race) — give back
                # the inflight slot so the scheduler doesn't deadlock.
                with lock:
                    inflight -= 1
                return
            fut.add_done_callback(lambda f, n=name: on_done(f, n))

        def on_done(future: Future, module_name: str):
            nonlocal completed_count, inflight

            filepath = resolve(dag.modules[module_name].filepath)
            try:
                result = future.result()
                tr = TraversalResult(module_name, filepath, result, None)
            except Exception as e:
                tr = TraversalResult(module_name, filepath, None, e)

            failed = tr.error is not None

            with lock:
                all_results.append(tr)
                completed_count += 1
                inflight -= 1

                if stop_on_failure and failed:
                    # Don't unlock successors — mark them as skipped
                    for succ in successors_of.get(module_name, []):
                        if succ in remaining_deps:
                            mark_skipped(succ)
                else:
                    # Decrement dep counts and collect newly ready modules.
                    # Skip-set modules that become ready are completed inline
                    # (no action) and their successors are cascaded.
                    cascade = [module_name]
                    while cascade:
                        current = cascade.pop()
                        for succ in successors_of.get(current, []):
                            if succ in remaining_deps and succ not in skipped:
                                remaining_deps[succ] -= 1
                                if remaining_deps[succ] == 0:
                                    if succ in skip_set:
                                        fp = resolve(dag.modules[succ].filepath)
                                        all_results.append(TraversalResult(succ, fp))
                                        completed_count += 1
                                        cascade.append(succ)
                                    else:
                                        heapq.heappush(
                                            ready_queue,
                                            (-depths.get(succ, 0), succ),
                                        )

                cc = completed_count
                sc = len(skipped)
                to_submit = _drain_ready()
                ic = inflight

                if cc + sc >= total:
                    done_event.set()

            if module_callback:
                module_callback(module_name, tr.result, tr.error)
            if progress_callback:
                progress_callback(cc, total - sc, ic)

            for name in to_submit:
                _do_submit(name)

        # Process skip modules before starting the executor.  We iterate in
        # topological order (BFS from zero-dep seeds) so that each skipped
        # module's successors have their dep counts correctly decremented.
        skip_set = skip or set()

        if skip_set:
            from collections import deque

            skip_queue: deque[str] = deque(
                name for name, count in remaining_deps.items()
                if count == 0 and name in skip_set
            )
            while skip_queue:
                name = skip_queue.popleft()
                filepath = resolve(dag.modules[name].filepath)
                all_results.append(TraversalResult(name, filepath))
                completed_count += 1
                for succ in successors_of.get(name, []):
                    if succ in remaining_deps:
                        remaining_deps[succ] -= 1
                        if remaining_deps[succ] == 0 and succ in skip_set:
                            skip_queue.append(succ)

            # Update display so it doesn't sit at [0/N] during skip processing.
            if progress_callback:
                progress_callback(completed_count, total, 0)

        executor = ThreadPoolExecutor(max_workers=max_workers)
        try:
            # Seed the priority queue with all zero-dep modules.
            seeds = [
                name for name, count in remaining_deps.items()
                if count == 0 and name not in skip_set
            ]
            if not seeds and completed_count < total:
                raise ValueError(
                    f"No modules with zero dependencies -- possible cycle in DAG "
                    f"({total} modules)"
                )
            if not seeds:
                done_event.set()

            with lock:
                for name in seeds:
                    heapq.heappush(ready_queue, (-depths.get(name, 0), name))
                to_submit = _drain_ready()

            for name in to_submit:
                _do_submit(name)

            # Update display to show inflight count now that seeds are submitted.
            if progress_callback and to_submit:
                with lock:
                    progress_callback(completed_count, total - len(skipped), inflight)

            # Wait until all modules are processed or skipped.
            # We cannot use executor.shutdown(wait=True) here because on_done
            # callbacks submit new futures — shutdown would reject them.
            # Use a timeout loop so the main thread can receive KeyboardInterrupt
            # (Event.wait() without timeout blocks signal delivery on Linux).
            while not done_event.wait(timeout=0.5):
                pass
            executor.shutdown(wait=True)
        except KeyboardInterrupt:
            self.shutdown_event.set()
            executor.shutdown(wait=False, cancel_futures=True)
            raise

        unprocessed = total - completed_count - len(skipped)
        if unprocessed > 0:
            unreached = [
                name
                for name, c in remaining_deps.items()
                if c > 0 and name not in skipped
            ]
            raise ValueError(
                f"Traversal incomplete: {completed_count}/{total} modules processed, "
                f"{len(skipped)} skipped, {unprocessed} unreached (possible cycle). "
                f"Examples: {unreached[:5]}"
            )

        return all_results


@dataclass
class ModuleInfo:
    """Information about a single module in the DAG."""

    name: str
    filepath: Path
    imports: list[str] = field(default_factory=list)
    importers: list[str] = field(default_factory=list)


@dataclass
class TraversalResult:
    """Result of processing a single module."""

    module_name: str
    filepath: Path
    result: object = None
    error: Exception | None = None


def _parse_all_imports(
    filepaths: list[Path], project_root: Path,
) -> dict[Path, list[str]]:
    """Parse imports for all files using ``lean --deps-json``.

    Returns a dict mapping each filepath to its list of imported module names.
    Files that fail to parse are recorded with empty imports and a warning
    is printed to stderr, so a single broken file does not abort the entire
    DAG build.

    The output entries are matched to input files by position (``lean`` emits
    one entry per input file in the same order).
    """
    cmd = ["lake", "env", "lean", "--deps-json", "--stdin"]
    stdin_data = "\n".join(str(f) for f in filepaths)
    proc = subprocess.run(
        cmd, input=stdin_data, capture_output=True, text=True, cwd=project_root,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"lean --deps-json failed (exit {proc.returncode}):\n{proc.stderr}"
        )

    data = json.loads(proc.stdout)
    entries = data["imports"]

    if len(entries) != len(filepaths):
        raise RuntimeError(
            f"lean --deps-json returned {len(entries)} entries "
            f"for {len(filepaths)} files"
        )

    result: dict[Path, list[str]] = {}
    for filepath, entry in zip(filepaths, entries):
        if entry.get("errors"):
            errors = "; ".join(entry["errors"])
            print(
                f"warning: lean --deps-json: {filepath}: {errors}",
                file=sys.stderr,
            )
        imports: list[str] = []
        if entry.get("result"):
            for imp in entry["result"]["imports"]:
                imports.append(imp["module"])
        result[filepath] = imports

    return result


def _filepath_to_module(filepath: str) -> str:
    """Convert a file path like Mathlib/Foo/Bar.lean to Mathlib.Foo.Bar."""
    return ".".join(Path(filepath).with_suffix("").parts)


class DAG:
    """The import DAG for a set of Lean modules."""

    def __init__(
        self,
        modules: dict[str, ModuleInfo] | None = None,
        project_root: Path | None = None,
    ):
        self.modules: dict[str, ModuleInfo] = modules or {}
        self.project_root: Path | None = project_root

    @staticmethod
    def from_directories(
        project_root: Path,
        directories: list[str] | None = None,
    ) -> "DAG":
        """Build DAG by parsing imports from .lean files in directories.

        Uses ``lean --deps-json`` to parse imports correctly.
        """
        if directories is None:
            directories = ["Mathlib", "MathlibTest", "Archive", "Counterexamples"]

        # Collect all .lean file paths (relative to project_root).
        rel_paths: list[Path] = []
        for directory in directories:
            dir_path = project_root / directory
            if not dir_path.exists():
                continue
            for root, _, files in os.walk(dir_path):
                for fname in files:
                    if not fname.endswith(".lean"):
                        continue
                    full_path = Path(root) / fname
                    rel_paths.append(full_path.relative_to(project_root))

        # Batch-parse imports using lean --deps-json.
        all_imports = _parse_all_imports(rel_paths, project_root)

        modules: dict[str, ModuleInfo] = {}
        for rel_path in rel_paths:
            module_name = _filepath_to_module(str(rel_path))
            imports = all_imports.get(rel_path, [])
            modules[module_name] = ModuleInfo(
                name=module_name,
                filepath=rel_path,
                imports=[i for i in imports if i != module_name],
            )

        # Build reverse edges (importers)
        for name, info in modules.items():
            for imp in info.imports:
                if imp in modules:
                    modules[imp].importers.append(name)

        return DAG(modules, project_root.resolve())

    def subset(self, module_names: set[str]) -> "DAG":
        """Return a sub-DAG containing only the specified modules."""
        new_modules: dict[str, ModuleInfo] = {}
        for name in module_names:
            if name not in self.modules:
                continue
            info = self.modules[name]
            new_modules[name] = ModuleInfo(
                name=name,
                filepath=info.filepath,
                imports=[i for i in info.imports if i in module_names],
                importers=[i for i in info.importers if i in module_names],
            )
        return DAG(new_modules, self.project_root)

    def forward_cone(self, seeds: set[str]) -> set[str]:
        """Return *seeds* plus all modules that transitively import any seed."""
        from collections import deque

        result: set[str] = set()
        queue: deque[str] = deque(s for s in seeds if s in self.modules)
        while queue:
            name = queue.popleft()
            if name in result:
                continue
            result.add(name)
            for imp in self.modules[name].importers:
                if imp in self.modules and imp not in result:
                    queue.append(imp)
        return result

    def levels_backward(self) -> list[list[str]]:
        """Compute levels for backward (downstream-first) traversal.

        Useful for display/reporting. DAGTraverser.traverse does not use
        this -- it schedules dynamically for maximum parallelism.

        Level 0 = modules not imported by any other module in the DAG.
        Level n+1 = modules whose importers are all at level <= n.
        """
        remaining_importers = {
            name: len(info.importers) for name, info in self.modules.items()
        }
        remaining = set(self.modules.keys())
        levels: list[list[str]] = []

        while remaining:
            level = sorted(m for m in remaining if remaining_importers[m] == 0)
            if not level:
                print(
                    f"warning: cycle in import DAG, dumping {len(remaining)} "
                    f"modules into final level",
                    file=sys.stderr,
                )
                levels.append(sorted(remaining))
                break
            levels.append(level)
            for m in level:
                remaining.discard(m)
                for imp in self.modules[m].imports:
                    if imp in remaining_importers:
                        remaining_importers[imp] -= 1

        return levels


def _compute_depths(
    successors_of: dict[str, list[str]],
    weights: dict[str, int] | None = None,
) -> dict[str, int]:
    """Compute the longest successor-chain length for each module.

    Without *weights*:
        depth[m] = 0 if m has no successors, else
        1 + max(depth[s] for s in successors_of[m]).

    With *weights*:
        w(m) = weights.get(m, 0)
        depth[m] = w(m) if m has no successors, else
        w(m) + max(depth[s] for s in successors_of[m]).

        Modules absent from *weights* (e.g. skip-set modules that are
        processed instantly) default to weight 0, so they don't inflate
        the critical-path estimate.

    Used to prioritise modules whose completion unblocks the costliest
    chains of future work, improving overall parallelism.

    Nodes involved in cycles (which shouldn't exist in a well-formed
    import graph) are assigned depth 0.
    """
    depths: dict[str, int] = {}
    visiting: set[str] = set()  # cycle detection

    for start in successors_of:
        if start in depths:
            continue
        # Iterative post-order DFS
        stack: list[tuple[str, bool]] = [(start, False)]
        while stack:
            node, processed = stack.pop()
            if processed:
                visiting.discard(node)
                succs = [s for s in successors_of.get(node, []) if s in depths]
                if weights is not None:
                    w = weights.get(node, 0)
                    depths[node] = (w + max(depths[s] for s in succs)) if succs else w
                else:
                    depths[node] = (1 + max(depths[s] for s in succs)) if succs else 0
                continue
            if node in depths:
                continue
            if node in visiting:
                # Cycle — assign depth 0 and don't recurse further.
                depths[node] = 0
                continue
            visiting.add(node)
            stack.append((node, True))
            for s in successors_of.get(node, []):
                if s not in depths and s in successors_of:
                    stack.append((s, False))

    return depths


def traverse_dag(
    dag: DAG,
    action: Callable[[str, Path], object],
    direction: str = "backward",
    **kwargs,
) -> list[TraversalResult]:
    """Convenience wrapper: create a one-off DAGTraverser and traverse."""
    return DAGTraverser().traverse(dag, action, direction, **kwargs)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


class Display:
    """ANSI progress display for DAG traversal.

    Subclass and override ``_status_line`` (and add an ``on_module``
    callback) to customise for a specific script.
    """

    def __init__(self):
        self.lock = Lock()
        self.completed = 0
        self.total = 0
        self.inflight = 0
        self.messages: list[str] = []
        self.displayed_lines = 0
        self.started = False

    def start(self, total: int):
        self.total = total
        self.started = True
        print(HIDE_CURSOR, end="", flush=True)
        self._redraw()

    def stop(self):
        if self.started:
            print(SHOW_CURSOR, end="", flush=True)
            self.started = False

    def _status_line(self) -> str:
        return f"[{self.completed}/{self.total}]  Working on: {self.inflight}"

    def _redraw(self):
        if not self.started:
            return
        if self.displayed_lines > 0:
            print(f"\033[{self.displayed_lines}A", end="")
        for msg in self.messages:
            print(CLEAR_LINE + msg)
        self.messages.clear()

        print(CLEAR_LINE + self._status_line(), flush=True)
        self.displayed_lines = 1

    def on_progress(self, completed: int, total: int, inflight: int):
        with self.lock:
            self.completed = completed
            self.total = total
            self.inflight = inflight
            self._redraw()


class _CliDisplay(Display):
    """Display subclass for the CLI that clears lines on stop."""

    def __init__(self):
        super().__init__()
        self.ok = 0
        self.fail = 0

    def stop(self):
        if self.started:
            if self.displayed_lines > 0:
                print(f"\033[{self.displayed_lines}A", end="")
                for _ in range(self.displayed_lines):
                    print(CLEAR_LINE)
                print(f"\033[{self.displayed_lines}A", end="", flush=True)
            print(SHOW_CURSOR, end="", flush=True)
            self.started = False

    def _status_line(self) -> str:
        return (
            f"[{self.completed}/{self.total}]  "
            f"Working on: {self.inflight}  ok: {self.ok}  fail: {self.fail}"
        )

    def on_module(self, module_name: str, result, error: Exception | None):
        with self.lock:
            if error:
                self.fail += 1
                self.messages.append(f"  \u2717 {module_name}: {error}")
            else:
                self.ok += 1
                self.messages.append(f"  \u2713 {module_name}")
            self._redraw()


class _CommandFailed(Exception):
    """Raised when a shell command exits with non-zero status."""

    def __init__(self, exit_code: int, output: str = ""):
        self.exit_code = exit_code
        self.output = output
        super().__init__(f"exit {exit_code}")


def _cli_main():
    parser = argparse.ArgumentParser(
        description="Run a command on each Lean module in import-DAG order.",
        epilog="Use {} in the command as a placeholder for the file path "
        "(or module name with --module).",
    )

    direction = parser.add_mutually_exclusive_group(required=True)
    direction.add_argument(
        "--forward",
        action="store_const",
        const="forward",
        dest="direction",
        help="Process upstream (roots) first",
    )
    direction.add_argument(
        "--backward",
        action="store_const",
        const="backward",
        dest="direction",
        help="Process downstream (leaves) first",
    )

    parser.add_argument(
        "command",
        help="Command template; {} is replaced with filepath or module name",
    )
    parser.add_argument(
        "--module",
        action="store_true",
        help="Replace {} with module name (Mathlib.Foo.Bar) instead of file path",
    )
    parser.add_argument(
        "-j",
        "--max-workers",
        type=int,
        default=None,
        help="Max parallel workers (default: cpu count)",
    )
    parser.add_argument(
        "--dir",
        type=Path,
        default=Path("."),
        help="Project root directory (default: cwd)",
    )
    parser.add_argument(
        "--directories",
        nargs="+",
        default=None,
        help="Directories to scan (default: Mathlib MathlibTest Archive Counterexamples)",
    )

    args = parser.parse_args()

    print("Building import DAG...", end="", flush=True)
    dag = DAG.from_directories(args.dir, args.directories)
    print(f" {len(dag.modules)} modules")

    use_module = args.module
    cmd_template = args.command

    def action(module_name: str, filepath: Path) -> int:
        replacement = module_name if use_module else str(filepath)
        cmd = cmd_template.replace("{}", shlex.quote(replacement))
        result = subprocess.run(
            cmd, shell=True, cwd=dag.project_root,
            capture_output=True, text=True,
        )
        if result.returncode != 0:
            raise _CommandFailed(result.returncode, result.stdout + result.stderr)
        return result.returncode

    display = _CliDisplay()
    display.start(len(dag.modules))

    try:
        results = traverse_dag(
            dag,
            action,
            direction=args.direction,
            max_workers=args.max_workers,
            module_callback=display.on_module,
            progress_callback=display.on_progress,
            stop_on_failure=True,
        )
    except KeyboardInterrupt:
        display.stop()
        print("Interrupted.")
        sys.exit(1)
    finally:
        display.stop()

    # Summary
    ok = sum(1 for r in results if r.error is None)
    failed = sum(1 for r in results if r.error is not None)
    skipped = len(dag.modules) - len(results)

    print(f"Done: {ok} ok, {failed} failed, {skipped} skipped")

    if failed:
        print(f"\nFailed modules:")
        for r in results:
            if r.error:
                print(f"  {r.module_name}: {r.error}")
                if isinstance(r.error, _CommandFailed) and r.error.output.strip():
                    for line in r.error.output.strip().splitlines():
                        print(f"    {line}")

    if skipped:
        processed = {r.module_name for r in results}
        skipped_names = sorted(set(dag.modules.keys()) - processed)
        print(f"\nSkipped modules ({skipped}):")
        for name in skipped_names[:20]:
            print(f"  {name}")
        if len(skipped_names) > 20:
            print(f"  ... and {len(skipped_names) - 20} more")

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    _cli_main()
