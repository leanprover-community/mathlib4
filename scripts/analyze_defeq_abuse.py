#!/usr/bin/env python3
"""
Analyze `set_option backward.isDefEq.respectTransparency false in` occurrences
using the `#defeq_abuse` diagnostic command.

For each occurrence, replaces it with `#defeq_abuse in`, type-checks the file
with `lake env lean` (no .oleans written), parses the diagnostics, and records
the results in a SQLite database.
"""

import argparse
import atexit
import hashlib
import json
import os
import re
import signal
import sqlite3
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from threading import Event, Lock

from dag_traversal import DAG
from set_option_utils import (
    PROJECT_DIR,
    removable_pattern,
    commented_pattern,
    lake_build_with_progress,
)

OPTION = "backward.isDefEq.respectTransparency"
PROGRESS_FILE = PROJECT_DIR / "scripts" / ".analyze_defeq_abuse_progress.jsonl"
RESULTS_DB = PROJECT_DIR / "scripts" / "defeq_abuse_results.db"

REMOVABLE_PAT = removable_pattern(OPTION)
COMMENTED_PAT = commented_pattern(OPTION)

# Regex for `set_option backward.isDefEq.respectTransparency false in` with
# optional trailing comment. Captures: leading whitespace, optional comment.
SET_OPTION_RE = re.compile(
    r"^(\s*)set_option backward\.isDefEq\.respectTransparency false in(.*)\n$"
)

# Lean diagnostic header: file:line:col: severity: message
DIAG_HEADER_RE = re.compile(
    r"^(.+?):(\d+):(\d+):\s*(info|warning|error):\s*(.*)"
)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class Occurrence:
    """A single set_option occurrence in a file."""
    line: int           # 1-indexed
    has_comment: bool
    comment: str        # trailing comment text (empty if none)


@dataclass
class Diagnostic:
    """A parsed diagnostic message from lean."""
    file: str
    line: int
    col: int
    severity: str
    message: str


@dataclass
class OccurrenceResult:
    """Result of analyzing one set_option occurrence."""
    file: str
    module: str
    line: int
    decl_header: str
    category: str       # removable, no_abuse, transition_failure,
                        # synth_failure, fails_regardless, unidentified,
                        # build_error, timeout, no_diagnostic
    kind: str = ""      # "command" or "tactic" or ""
    failures: list[str] = field(default_factory=list)
    synth_apps: list[dict] = field(default_factory=list)
    raw_message: str = ""
    elapsed_s: float = 0.0


@dataclass
class FileResult:
    """Aggregated result for one file."""
    occurrences: list[OccurrenceResult] = field(default_factory=list)
    removable: int = 0
    no_abuse: int = 0
    transition: int = 0
    synth: int = 0
    fails_regardless: int = 0
    other: int = 0
    errors: int = 0


# ---------------------------------------------------------------------------
# Progress management
# ---------------------------------------------------------------------------

_progress_lock = Lock()


def _current_toolchain() -> str:
    return (PROJECT_DIR / "lean-toolchain").read_text().strip()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_progress() -> dict[str, str] | None:
    """Load progress file. Returns {module: sha256} or None if invalid."""
    if not PROGRESS_FILE.exists():
        return None
    progress: dict[str, str] = {}
    toolchain = _current_toolchain()
    with open(PROGRESS_FILE) as f:
        for i, line in enumerate(f):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if i == 0:
                if record.get("toolchain") != toolchain:
                    return None
                continue
            if "module" in record and "sha256" in record:
                progress[record["module"]] = record["sha256"]
    return progress


def init_progress():
    """Write toolchain header to a fresh progress file."""
    with open(PROGRESS_FILE, "w") as f:
        json.dump({"toolchain": _current_toolchain()}, f)
        f.write("\n")


def save_progress(module: str, sha256: str):
    """Append a completion record (thread-safe)."""
    with _progress_lock:
        with open(PROGRESS_FILE, "a") as f:
            json.dump({"module": module, "sha256": sha256}, f)
            f.write("\n")


# ---------------------------------------------------------------------------
# Results I/O (SQLite)
# ---------------------------------------------------------------------------

_results_lock = Lock()
_db_conn: sqlite3.Connection | None = None


def _get_db() -> sqlite3.Connection:
    """Return the shared database connection (created on first call)."""
    global _db_conn
    if _db_conn is None:
        _db_conn = sqlite3.connect(str(RESULTS_DB), check_same_thread=False)
        _db_conn.execute("PRAGMA journal_mode=WAL")
        _db_conn.execute("PRAGMA synchronous=NORMAL")
    return _db_conn


def init_results():
    """Create the SQLite database and tables."""
    conn = _get_db()
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS meta (
            key   TEXT PRIMARY KEY,
            value TEXT
        );
        CREATE TABLE IF NOT EXISTS occurrences (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            file        TEXT NOT NULL,
            module      TEXT NOT NULL,
            line        INTEGER NOT NULL,
            decl_header TEXT,
            category    TEXT NOT NULL,
            kind        TEXT,
            raw_message TEXT,
            elapsed_s   REAL,
            UNIQUE(file, line)
        );
        CREATE TABLE IF NOT EXISTS failures (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            occurrence_id INTEGER NOT NULL REFERENCES occurrences(id),
            failure       TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS synth_apps (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            occurrence_id INTEGER NOT NULL REFERENCES occurrences(id),
            app           TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS synth_app_failures (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            synth_app_id INTEGER NOT NULL REFERENCES synth_apps(id),
            failure      TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_occurrences_module ON occurrences(module);
        CREATE INDEX IF NOT EXISTS idx_occurrences_category ON occurrences(category);
        CREATE INDEX IF NOT EXISTS idx_failures_occ ON failures(occurrence_id);
        CREATE INDEX IF NOT EXISTS idx_synth_apps_occ ON synth_apps(occurrence_id);
        CREATE INDEX IF NOT EXISTS idx_synth_app_failures_sa ON synth_app_failures(synth_app_id);
    """)
    conn.execute(
        "INSERT OR REPLACE INTO meta (key, value) VALUES (?, ?)",
        ("toolchain", _current_toolchain()),
    )
    conn.execute(
        "INSERT OR REPLACE INTO meta (key, value) VALUES (?, ?)",
        ("timestamp", time.strftime("%Y-%m-%dT%H:%M:%S")),
    )
    conn.commit()


def append_results(results: list[OccurrenceResult]):
    """Insert occurrence results into the database (thread-safe)."""
    with _results_lock:
        conn = _get_db()
        for r in results:
            cur = conn.execute(
                """INSERT OR REPLACE INTO occurrences
                   (file, module, line, decl_header, category, kind,
                    raw_message, elapsed_s)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                (r.file, r.module, r.line, r.decl_header, r.category,
                 r.kind, r.raw_message, r.elapsed_s),
            )
            occ_id = cur.lastrowid
            # Clear any previous sub-records for this occurrence
            conn.execute(
                "DELETE FROM failures WHERE occurrence_id = ?", (occ_id,))
            conn.execute(
                """DELETE FROM synth_app_failures WHERE synth_app_id IN
                   (SELECT id FROM synth_apps WHERE occurrence_id = ?)""",
                (occ_id,))
            conn.execute(
                "DELETE FROM synth_apps WHERE occurrence_id = ?", (occ_id,))
            for f in r.failures:
                conn.execute(
                    "INSERT INTO failures (occurrence_id, failure) VALUES (?, ?)",
                    (occ_id, f),
                )
            for sa in r.synth_apps:
                sa_cur = conn.execute(
                    "INSERT INTO synth_apps (occurrence_id, app) VALUES (?, ?)",
                    (occ_id, sa.get("app", "")),
                )
                sa_id = sa_cur.lastrowid
                for sf in sa.get("failures", []):
                    conn.execute(
                        "INSERT INTO synth_app_failures (synth_app_id, failure) "
                        "VALUES (?, ?)",
                        (sa_id, sf),
                    )
        conn.commit()


def delete_module_results(module: str):
    """Delete all DB rows for a module (stale data cleanup)."""
    with _results_lock:
        conn = _get_db()
        occ_ids = [
            r[0]
            for r in conn.execute(
                "SELECT id FROM occurrences WHERE module = ?", (module,)
            )
        ]
        if not occ_ids:
            return
        placeholders = ",".join("?" * len(occ_ids))
        conn.execute(
            f"""DELETE FROM synth_app_failures WHERE synth_app_id IN
                (SELECT id FROM synth_apps WHERE occurrence_id IN ({placeholders}))""",
            occ_ids,
        )
        conn.execute(
            f"DELETE FROM synth_apps WHERE occurrence_id IN ({placeholders})",
            occ_ids,
        )
        conn.execute(
            f"DELETE FROM failures WHERE occurrence_id IN ({placeholders})",
            occ_ids,
        )
        conn.execute(
            f"DELETE FROM occurrences WHERE id IN ({placeholders})",
            occ_ids,
        )
        conn.commit()


# ---------------------------------------------------------------------------
# DAG helpers
# ---------------------------------------------------------------------------

def _transitive_importers(dag: DAG, module_name: str) -> set[str]:
    """Return all modules that transitively import the given module (BFS over importers)."""
    visited: set[str] = {module_name}
    queue = [module_name]
    while queue:
        current = queue.pop()
        info = dag.modules.get(current)
        if info is None:
            continue
        for importer in info.importers:
            if importer not in visited:
                visited.add(importer)
                queue.append(importer)
    return visited


# ---------------------------------------------------------------------------
# Scanning
# ---------------------------------------------------------------------------

def scan_files(dag: DAG) -> dict[str, list[Occurrence]]:
    """Find files with set_option ... false in lines.

    Returns dict of module_name -> list of Occurrence.
    """
    results: dict[str, list[Occurrence]] = {}
    for name, info in dag.modules.items():
        filepath = dag.project_root / info.filepath
        if not filepath.exists():
            continue
        lines = filepath.read_text().splitlines(keepends=True)
        occurrences: list[Occurrence] = []
        for i, line in enumerate(lines):
            m = SET_OPTION_RE.match(line)
            if m:
                comment_part = m.group(2).strip()
                has_comment = comment_part.startswith("--")
                occurrences.append(Occurrence(
                    line=i + 1,
                    has_comment=has_comment,
                    comment=comment_part,
                ))
        if occurrences:
            results[name] = occurrences
    return results


def get_decl_header(lines: list[str], set_option_line: int) -> str:
    """Get the declaration header following the set_option line.

    Skips chained set_options to find the actual declaration.
    """
    i = set_option_line  # 0-indexed line after the set_option
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("set_option ") and stripped.endswith(" in"):
            i += 1
            continue
        if stripped:
            # Return first 120 chars of the declaration line
            return stripped[:120]
        i += 1
    return ""


# ---------------------------------------------------------------------------
# File transformation
# ---------------------------------------------------------------------------

def replace_set_options(lines: list[str]) -> list[str]:
    """Replace set_option ... false in with #defeq_abuse in.

    Preserves leading whitespace and trailing comments.
    Returns new list of lines (same count).
    """
    result = []
    for line in lines:
        m = SET_OPTION_RE.match(line)
        if m:
            indent = m.group(1)
            rest = m.group(2)  # trailing comment or empty
            result.append(f"{indent}#defeq_abuse in{rest}\n")
        else:
            result.append(line)
    return result


# ---------------------------------------------------------------------------
# Diagnostic parsing
# ---------------------------------------------------------------------------

def parse_diagnostics(output: str) -> list[Diagnostic]:
    """Parse lean output into structured diagnostics."""
    diagnostics: list[Diagnostic] = []
    current: Diagnostic | None = None
    for line in output.splitlines():
        m = DIAG_HEADER_RE.match(line)
        if m:
            if current:
                diagnostics.append(current)
            current = Diagnostic(
                file=m.group(1),
                line=int(m.group(2)),
                col=int(m.group(3)),
                severity=m.group(4),
                message=m.group(5),
            )
        elif current:
            current.message += "\n" + line
    if current:
        diagnostics.append(current)
    return diagnostics


# Emoji used in #defeq_abuse output (may include variation selector)
CROSS_EMOJI = "❌"

# Patterns for parsing failure details
FAILURE_LINE_RE = re.compile(r"^\s*❌️?\s*(.+=\?=.+)$", re.MULTILINE)
SYNTH_APP_RE = re.compile(r"^\s*❌️?\s*(apply\s+@.+?\s+to\s+.+)$", re.MULTILINE)


def classify_diagnostic(diag: Diagnostic) -> dict:
    """Classify a #defeq_abuse diagnostic into structured result fields."""
    msg = diag.message

    if "#defeq_abuse:" not in msg:
        return {"category": "build_error", "raw_message": msg}

    # Extract kind (command/tactic)
    kind_match = re.search(r"#defeq_abuse:\s+(\w+)", msg)
    kind = kind_match.group(1) if kind_match else ""

    # Check failure categories first — a message may contain both failure
    # and "No abuse detected" (from chained set_options producing multiple
    # diagnostics on the same line), so failures take priority.
    if "isDefEq checks are the root causes" in msg:
        failures = parse_isdefeq_failures(msg)
        return {
            "category": "transition_failure",
            "kind": kind,
            "failures": failures,
            "raw_message": msg,
        }

    if "synthesis applications fail" in msg:
        synth_apps = parse_synth_failures(msg)
        all_failures = [f for app in synth_apps for f in app["failures"]]
        return {
            "category": "synth_failure",
            "kind": kind,
            "failures": all_failures,
            "synth_apps": synth_apps,
            "raw_message": msg,
        }

    if "fails regardless" in msg:
        return {"category": "fails_regardless", "kind": kind, "raw_message": msg}

    if "Could not identify specific failing" in msg:
        return {"category": "unidentified", "kind": kind, "raw_message": msg}

    if "No abuse detected" in msg:
        return {"category": "no_abuse", "kind": kind, "raw_message": msg}

    # Fallback: it's a #defeq_abuse message but doesn't match known patterns
    return {"category": "unidentified", "kind": kind, "raw_message": msg}


def parse_isdefeq_failures(msg: str) -> list[str]:
    """Extract 'LHS =?= RHS' failure strings."""
    return [m.group(1).strip() for m in FAILURE_LINE_RE.finditer(msg)]


def parse_synth_failures(msg: str) -> list[dict]:
    """Extract structured synth failures.

    Returns list of {"app": "apply @X to Y", "failures": ["LHS =?= RHS", ...]}
    """
    result: list[dict] = []
    lines = msg.split("\n")
    current_app: dict | None = None

    for line in lines:
        stripped = line.strip()
        if not stripped.startswith(CROSS_EMOJI):
            continue

        # Remove emoji prefix
        content = re.sub(r"^❌️?\s*", "", stripped)

        if content.startswith("apply "):
            # New synthesis application
            if current_app:
                result.append(current_app)
            current_app = {"app": content, "failures": []}
        elif "=?=" in content and current_app is not None:
            current_app["failures"].append(content)
        elif "=?=" in content:
            # Failure outside a synth app context
            if not result:
                result.append({"app": "", "failures": []})
            result[-1]["failures"].append(content)

    if current_app:
        result.append(current_app)
    return result


# ---------------------------------------------------------------------------
# lean invocation
# ---------------------------------------------------------------------------

def lean_check(
    filepath: Path,
    project_dir: Path,
    timeout: int,
    shutdown_event,
) -> tuple[bool, str, float]:
    """Type-check a file with `lake env lean`. No .oleans written.

    Returns (success, output, elapsed_seconds).
    """
    if shutdown_event and shutdown_event.is_set():
        raise KeyboardInterrupt("shutdown requested")

    start = time.monotonic()
    proc = subprocess.Popen(
        ["lake", "env", "lean", str(filepath)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        cwd=project_dir,
        start_new_session=True,
    )
    try:
        deadline = start + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                elapsed = time.monotonic() - start
                return False, "Timed out", elapsed
            try:
                stdout, _ = proc.communicate(timeout=min(remaining, 0.5))
                elapsed = time.monotonic() - start
                return proc.returncode == 0, stdout, elapsed
            except subprocess.TimeoutExpired:
                if shutdown_event and shutdown_event.is_set():
                    raise KeyboardInterrupt("shutdown requested")
    finally:
        if proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                proc.kill()
            proc.wait()


# ---------------------------------------------------------------------------
# Crash-safe inflight tracking
# ---------------------------------------------------------------------------

class _InflightTracker:
    """Track files currently being modified so they can be reverted on crash."""

    def __init__(self):
        self._lock = Lock()
        self._inflight: dict[Path, str] = {}
        atexit.register(self._revert_all)

    def register(self, path: Path, content: str):
        with self._lock:
            self._inflight[path] = content

    def unregister(self, path: Path):
        with self._lock:
            self._inflight.pop(path, None)

    def _revert_all(self):
        with self._lock:
            for path, content in self._inflight.items():
                try:
                    path.write_text(content)
                except Exception:
                    pass


# ---------------------------------------------------------------------------
# Core processing
# ---------------------------------------------------------------------------

def make_process_file(
    occurrence_map: dict[str, list[Occurrence]],
    timeout: int,
    shutdown_event: Event,
    inflight: "_InflightTracker",
):
    """Create the per-file action callback."""

    def process_file(module_name: str, filepath: Path) -> FileResult:
        occurrences = occurrence_map.get(module_name, [])
        if not occurrences:
            save_progress(module_name, file_sha256(filepath))
            return FileResult()

        original_text = filepath.read_text()
        original_lines = original_text.splitlines(keepends=True)

        # Collect decl headers before modifying
        decl_headers: dict[int, str] = {}
        raw_lines = original_text.splitlines()
        for occ in occurrences:
            decl_headers[occ.line] = get_decl_header(raw_lines, occ.line)

        # --- Pass 1: Replace with #defeq_abuse in ---
        inflight.register(filepath, original_text)
        try:
            modified_lines = replace_set_options(original_lines)
            filepath.write_text("".join(modified_lines))

            success, output, elapsed = lean_check(
                filepath, PROJECT_DIR, timeout, shutdown_event,
            )

            filepath.write_text(original_text)
        except BaseException:
            filepath.write_text(original_text)
            raise
        finally:
            inflight.unregister(filepath)

        # Parse diagnostics
        diagnostics = parse_diagnostics(output)

        defeq_diags: dict[int, Diagnostic] = {}
        for diag in diagnostics:
            if "#defeq_abuse:" in diag.message:
                defeq_diags[diag.line] = diag

        # Classify each occurrence
        classified_list: list[dict] = []
        for occ in occurrences:
            diag = defeq_diags.get(occ.line)
            if diag:
                classified_list.append(classify_diagnostic(diag))
            elif not success and "Timed out" in output:
                classified_list.append({"category": "timeout", "raw_message": ""})
            elif not success:
                classified_list.append(
                    {"category": "build_error", "raw_message": output[:500]})
            else:
                classified_list.append(
                    {"category": "no_diagnostic", "raw_message": ""})

        # --- Pass 2: Verify removability of no_abuse / no_diagnostic ---
        removable_indices = [
            i for i, c in enumerate(classified_list)
            if c.get("category") in ("no_abuse", "no_diagnostic")
        ]

        if removable_indices:
            removable_line_nums = {occurrences[i].line for i in removable_indices}
            verify_lines = list(original_lines)
            for line_num in removable_line_nums:
                verify_lines[line_num - 1] = "\n"

            inflight.register(filepath, original_text)
            try:
                filepath.write_text("".join(verify_lines))
                verify_ok, _, _ = lean_check(
                    filepath, PROJECT_DIR, timeout, shutdown_event,
                )
                filepath.write_text(original_text)
            except BaseException:
                filepath.write_text(original_text)
                raise
            finally:
                inflight.unregister(filepath)

            if verify_ok:
                for i in removable_indices:
                    classified_list[i]["category"] = "removable"

        # Build results
        file_result = FileResult()
        for occ, cls in zip(occurrences, classified_list):
            result = OccurrenceResult(
                file=str(filepath.relative_to(PROJECT_DIR)),
                module=module_name,
                line=occ.line,
                decl_header=decl_headers.get(occ.line, ""),
                category=cls.get("category", ""),
                kind=cls.get("kind", ""),
                failures=cls.get("failures", []),
                synth_apps=cls.get("synth_apps", []),
                raw_message=cls.get("raw_message", ""),
                elapsed_s=round(elapsed, 1),
            )
            file_result.occurrences.append(result)

            cat = result.category
            if cat == "removable":
                file_result.removable += 1
            elif cat == "no_abuse":
                file_result.no_abuse += 1
            elif cat == "transition_failure":
                file_result.transition += 1
            elif cat == "synth_failure":
                file_result.synth += 1
            elif cat == "fails_regardless":
                file_result.fails_regardless += 1
            elif cat in ("build_error", "timeout"):
                file_result.errors += 1
            else:
                file_result.other += 1

        # Save
        append_results(file_result.occurrences)
        save_progress(module_name, file_sha256(filepath))

        return file_result

    return process_file


# ---------------------------------------------------------------------------
# Display
# ---------------------------------------------------------------------------

HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"
CLEAR_LINE = "\033[2K"


class _AnalyzeDisplay:
    """Progress display for the analysis."""

    def __init__(self, total: int):
        self.lock = Lock()
        self.completed = 0
        self.total = total
        self.removable = 0
        self.no_abuse = 0
        self.transition = 0
        self.synth = 0
        self.fails_regardless = 0
        self.other = 0
        self.errors = 0
        self.messages: list[str] = []
        self.displayed_lines = 0
        print(HIDE_CURSOR, end="", flush=True)
        self._redraw()

    def stop(self):
        print(SHOW_CURSOR, end="", flush=True)

    def _status_line(self) -> str:
        return (
            f"[{self.completed}/{self.total}]  "
            f"removable: {self.removable}  clean: {self.no_abuse}  "
            f"defeq: {self.transition}  synth: {self.synth}  "
            f"both: {self.fails_regardless}  "
            f"other: {self.other}  err: {self.errors}"
        )

    def _redraw(self):
        if self.displayed_lines > 0:
            print(f"\033[{self.displayed_lines}A", end="")
        for msg in self.messages:
            print(CLEAR_LINE + msg)
        self.messages.clear()
        print(CLEAR_LINE + self._status_line(), flush=True)
        self.displayed_lines = 1

    def on_complete(
        self,
        module_name: str,
        result: FileResult | None,
        error: Exception | None,
    ):
        with self.lock:
            self.completed += 1
            if result:
                self.removable += result.removable
                self.no_abuse += result.no_abuse
                self.transition += result.transition
                self.synth += result.synth
                self.fails_regardless += result.fails_regardless
                self.other += result.other
                self.errors += result.errors
                n = len(result.occurrences)
                if result.errors > 0:
                    sym = "!"
                elif result.transition > 0 or result.synth > 0:
                    sym = "~"
                elif result.removable + result.no_abuse == n:
                    sym = "\u2713"
                else:
                    sym = "\u00b7"
                parts = []
                if result.removable:
                    parts.append(f"rm:{result.removable}")
                if result.no_abuse:
                    parts.append(f"clean:{result.no_abuse}")
                if result.transition:
                    parts.append(f"defeq:{result.transition}")
                if result.synth:
                    parts.append(f"synth:{result.synth}")
                if result.fails_regardless:
                    parts.append(f"both:{result.fails_regardless}")
                if result.other:
                    parts.append(f"other:{result.other}")
                if result.errors:
                    parts.append(f"err:{result.errors}")
                detail = " ".join(parts)
                self.messages.append(f"  {sym} {module_name} {detail}")
            elif error:
                self.errors += 1
                self.messages.append(f"  ! {module_name}: {error}")
            self._redraw()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def print_summary(
    total_files: int,
    removable: int,
    no_abuse: int,
    transition: int,
    synth: int,
    fails_regardless: int,
    other: int,
    errors: int,
    duration: float,
):
    total_occ = (removable + no_abuse + transition + synth +
                 fails_regardless + other + errors)
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Files processed:        {total_files}")
    print(f"  Total occurrences:      {total_occ}")
    print(f"  Removable (verified):   {removable}")
    print(f"  No abuse (unverified):  {no_abuse}")
    print(f"  Transition failures:    {transition}")
    print(f"  Synthesis failures:     {synth}")
    print(f"  Fails regardless:       {fails_regardless}")
    print(f"  Other/unidentified:     {other}")
    print(f"  Errors/timeouts:        {errors}")
    print(f"  Duration:               {duration:.0f}s")
    print(f"  Results:                {RESULTS_DB}")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze set_option backward.isDefEq.respectTransparency "
                    "false in occurrences using #defeq_abuse"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Scan and report without running lean",
    )
    parser.add_argument(
        "--max-workers",
        type=int,
        default=None,
        help="Max parallel workers (default: cpu_count)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1200,
        help="Timeout per module in seconds (default: 1200)",
    )
    parser.add_argument(
        "--files",
        nargs="*",
        help="Only process these files (paths relative to project root)",
    )
    parser.add_argument(
        "--no-initial",
        action="store_true",
        help="Skip the initial lake build",
    )
    parser.add_argument(
        "--no-resume",
        action="store_true",
        help="Ignore progress from a previous interrupted run",
    )
    args = parser.parse_args()

    start_time = time.time()

    # Step 1: build DAG
    print("Building import DAG...", flush=True)
    full_dag = DAG.from_directories(PROJECT_DIR)
    print(f"  {len(full_dag.modules)} modules parsed")

    # Step 2: scan for occurrences
    print("Scanning for set_option occurrences...", flush=True)
    occurrence_map = scan_files(full_dag)

    # Filter to modules that transitively import Mathlib.Tactic.Common
    # (which provides #defeq_abuse), and exclude test files.
    REQUIRED_IMPORT = "Mathlib.Tactic.Common"
    if REQUIRED_IMPORT in full_dag.modules:
        downstream = _transitive_importers(full_dag, REQUIRED_IMPORT)
        before = len(occurrence_map)
        occurrence_map = {k: v for k, v in occurrence_map.items()
                         if k in downstream}
        skipped = before - len(occurrence_map)
        if skipped:
            print(f"  Skipped {skipped} files not downstream of {REQUIRED_IMPORT}")

    # Exclude test files
    before = len(occurrence_map)
    occurrence_map = {k: v for k, v in occurrence_map.items()
                     if not k.startswith("MathlibTest.")}
    skipped = before - len(occurrence_map)
    if skipped:
        print(f"  Skipped {skipped} test files")

    if args.files:
        requested = set()
        for f in args.files:
            mod = f.replace("/", ".").removesuffix(".lean")
            requested.add(mod)
        occurrence_map = {k: v for k, v in occurrence_map.items() if k in requested}

    total_occurrences = sum(len(v) for v in occurrence_map.values())
    print(f"  {len(occurrence_map)} files with {total_occurrences} occurrences")

    # Step 3: load/manage progress — skip unchanged files, purge stale data
    resumed = 0
    if not args.no_resume:
        progress = load_progress()
        if progress:
            to_skip = []
            stale = []
            for name in list(occurrence_map):
                if name in progress:
                    fp = full_dag.project_root / full_dag.modules[name].filepath
                    if fp.exists() and file_sha256(fp) == progress[name]:
                        to_skip.append(name)
                    else:
                        # File changed since last run — purge old DB rows
                        stale.append(name)
            for name in to_skip:
                del occurrence_map[name]
            # Purge DB rows for changed files so they get fresh data
            if not args.dry_run:
                for name in stale:
                    delete_module_results(name)
            # Also purge modules that are in the DB but no longer have
            # any occurrences (e.g. set_option was removed entirely).
            # Only do this for full scans — --files restricts the
            # occurrence_map and would incorrectly mark everything else
            # as vanished.
            if not args.dry_run and not args.files and RESULTS_DB.exists():
                init_results()
                db_modules = {
                    r[0]
                    for r in _get_db().execute(
                        "SELECT DISTINCT module FROM occurrences"
                    )
                }
                vanished = db_modules - set(occurrence_map) - set(to_skip)
                for name in vanished:
                    delete_module_results(name)
                if vanished:
                    print(
                        f"  Purged {len(vanished)} modules whose"
                        f" set_option lines were removed"
                    )
            if stale:
                print(
                    f"  {'Would purge' if args.dry_run else 'Purged'}"
                    f" stale DB entries for {len(stale)}"
                    f" changed modules"
                )
            resumed = len(to_skip)
            if resumed:
                total_occurrences = sum(len(v) for v in occurrence_map.values())
                print(
                    f"  Resuming: skipped {resumed} already-processed modules"
                    f" ({len(occurrence_map)} remaining, "
                    f"{total_occurrences} occurrences)"
                )

    if not occurrence_map:
        print("Nothing to do.")
        return

    if args.dry_run:
        # Show distribution
        by_count: dict[int, int] = {}
        for occs in occurrence_map.values():
            n = len(occs)
            by_count[n] = by_count.get(n, 0) + 1
        print(f"\nDistribution of occurrences per file:")
        for n in sorted(by_count):
            print(f"  {n} occurrence(s): {by_count[n]} files")
        print(f"\nTotal: {len(occurrence_map)} files, {total_occurrences} occurrences")
        print("(dry run — no changes made)")
        return

    # Step 4: initial build
    if not args.no_initial:
        print("Running initial build to ensure .oleans are fresh...", flush=True)
        returncode, _ = lake_build_with_progress(PROJECT_DIR)
        if returncode != 0:
            print("  (initial build had errors — continuing anyway)")

    # Step 5: initialize progress and results files
    if not PROGRESS_FILE.exists() or args.no_resume:
        init_progress()
    if args.no_resume and RESULTS_DB.exists():
        RESULTS_DB.unlink()
    init_results()  # creates tables if needed, updates meta

    # Step 6: process all target modules in parallel
    max_workers = args.max_workers or os.cpu_count() or 4
    shutdown_event = Event()
    inflight = _InflightTracker()
    action = make_process_file(occurrence_map, args.timeout, shutdown_event, inflight)

    target_modules = list(occurrence_map.keys())
    display = _AnalyzeDisplay(len(target_modules))

    try:
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {}
            for mod_name in target_modules:
                filepath = full_dag.project_root / full_dag.modules[mod_name].filepath
                future = executor.submit(action, mod_name, filepath)
                futures[future] = mod_name

            for future in as_completed(futures):
                mod_name = futures[future]
                try:
                    result = future.result()
                    display.on_complete(mod_name, result, None)
                except Exception as exc:
                    display.on_complete(mod_name, None, exc)
    except KeyboardInterrupt:
        shutdown_event.set()
        display.stop()
        print("\nInterrupted.", flush=True)
        sys.exit(1)
    finally:
        display.stop()

    # Step 7: summarize
    duration = time.time() - start_time
    print_summary(
        total_files=len(target_modules),
        removable=display.removable,
        no_abuse=display.no_abuse,
        transition=display.transition,
        synth=display.synth,
        fails_regardless=display.fails_regardless,
        other=display.other,
        errors=display.errors,
        duration=duration,
    )


if __name__ == "__main__":
    main()
