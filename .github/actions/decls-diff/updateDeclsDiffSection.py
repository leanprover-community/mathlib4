#!/usr/bin/env python3
"""Patch the `#### Declarations diff` section of an existing `### PR summary`
comment with a Lean-aware diff.

Inputs (environment variables):
    GH_TOKEN       passed through to the `gh` CLI
    REPO           `owner/repo`
    PR_HEAD_SHA    head SHA of the PR (the workflow_run head_sha)
    PR_NUMBER      PR number (optional; resolved from PR_HEAD_SHA when empty)
    MODE           `success` (default) or `warning`
    DIFF_FILE      success mode: path to the `+NAME` / `-NAME` diff
    PLUS, MINUS    success mode: counts of `+`/`-` lines
    DEFAULT_BRANCH warning mode: default branch shown in the rebase suggestion
                     (default: `master`)

Modes:
    success — replace the section between `<!-- DECLS_DIFF_BEGIN -->` and
              `<!-- DECLS_DIFF_END -->` (or fall back to a header-based
              detection of `#### Declarations diff`) with a freshly-built
              Lean-aware section.
    warning — append a single explanatory blockquote inside the existing
              section. Idempotent via the `WARNING_MARKER` sentinel.

The comment is PATCHed via `gh api -X PATCH ... --input -`.

Exit codes:
    0 — patched, or skipped because there was nothing to patch
    1 — non-recoverable error (gh CLI failure, malformed env, ...)
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

BEGIN = "<!-- DECLS_DIFF_BEGIN -->"
END   = "<!-- DECLS_DIFF_END -->"
WARNING_MARKER = "<!-- DECLS_DIFF_WARNING -->"
PR_SUMMARY_PREFIX = "### PR summary"
# Newline-count threshold above which the rendered section is wrapped in
# `<details>`. Matches `PR_summary.yml`'s heuristic.
DETAILS_LINE_THRESHOLD = 15


def gh_json(*args: str) -> object:
    """Run `gh api …` and parse the JSON result."""
    out = subprocess.run(
        ["gh", "api", *args],
        check=True, text=True, capture_output=True,
    ).stdout
    return json.loads(out)


def short(sha: str) -> str:
    return sha[:7] if len(sha) >= 7 else sha


def build_section(plus: int, minus: int, diff_text: str, head_sha: str) -> str:
    """Render the Lean-aware `#### Declarations diff` section, including
    sentinel markers and the post-build stamp. When the rendered body has
    more than `DETAILS_LINE_THRESHOLD` newlines, the section is wrapped in
    `<details>`; otherwise the heading and body render inline."""
    diff_lines = diff_text.splitlines()
    total = len(diff_lines)
    preview_lines = diff_lines[:200]
    preview = "\n".join(preview_lines)
    diff_note = ""
    if total > 200:
        diff_note = f"\n_(showing first 200 of {total} lines)_\n"

    body_parts = [
        f"> ✅ **Lean-aware diff** — post-build, computed from the Lean environment "
        f"(commit `{short(head_sha)}`).",
        "",
        f"* **+{plus}** new declarations",
        f"* **−{minus}** removed declarations",
    ]
    if total > 0:
        body_parts += [
            diff_note,
            "```diff",
            preview,
            "```",
        ]
    else:
        body_parts += ["", "_No declaration differences._"]
    body = "\n".join(body_parts)

    # Match PR_summary.yml: `wc -l` counts newlines, not lines, so we do the same.
    if body.count("\n") > DETAILS_LINE_THRESHOLD:
        wrapped = "\n".join([
            "<details><summary>",
            "",
            "#### Declarations diff",
            "",
            "</summary>",
            "",
            body,
            "",
            "</details>",
        ])
    else:
        wrapped = "\n".join([
            "#### Declarations diff",
            "",
            body,
        ])

    return "\n".join([BEGIN, wrapped, END])


def build_warning(default_branch: str) -> str:
    """Render the `Lean-aware diff unavailable` `<details>` block. The leading
    `WARNING_MARKER` HTML comment makes the patcher idempotent on re-runs."""
    return "\n".join([
        WARNING_MARKER,
        "<details><summary>",
        "",
        "⚠️ **Lean-aware diff unavailable**",
        "",
        "</summary>",
        "",
        f"The Mathlib cache for this PR's merge-base isn't on the server "
        f"(typically because the merge-base is a bors-batch intermediate that "
        f"CI never built). Merge `{default_branch}` into this PR and push to "
        f"retrigger the build; the post-build action will then run.",
        "",
        "</details>",
    ])


def _normalize_section_spacing(body: str) -> str:
    """Collapse any run of newlines immediately above BEGIN and immediately
    below END to exactly one blank line. Idempotent."""
    body = re.sub(
        r"(\S)[ \t]*\n+(?=" + re.escape(BEGIN) + r")",
        r"\1\n\n",
        body, count=1,
    )
    body = re.sub(
        re.escape(END) + r"[ \t]*\n+(?=\S)",
        END + "\n\n",
        body, count=1,
    )
    return body


def splice(body: str, new_section: str) -> tuple[str, str]:
    """Success-mode splice: replace the entire Declarations-diff section.
    Returns `(new_body, mode)` where `mode` is one of `markers`,
    `wrapped-header-fallback`, `header-fallback`, `append`."""

    # The optional `<details><summary>` prefix absorbs an orphan opener left
    # by older patcher revisions before BEGIN.
    marker_re = re.compile(
        r"(?:<details>\s*<summary>\s*\n+\s*)?"
        + re.escape(BEGIN) + r".*?" + re.escape(END),
        re.DOTALL,
    )
    if marker_re.search(body):
        return _normalize_section_spacing(
            marker_re.sub(new_section, body, count=1)
        ), "markers"

    # Wrapped form: `<details><summary>#### Declarations diff</summary>…</details>`
    # followed by `---`/`####`/EOF. The non-greedy `[\s\S]*?` lets nested
    # `<details>...</details>` inside the content pass through unmatched,
    # because the lookahead only succeeds at the OUTER `</details>` (the
    # one followed by a section boundary).
    wrapped_re = re.compile(
        r"<details>\s*<summary>\s*\n+\s*#### Declarations diff\s*\n+\s*</summary>"
        r"[\s\S]*?</details>(?=\s*\n+(?:---\s*$|####\s|\Z))",
        re.MULTILINE,
    )
    if wrapped_re.search(body):
        return _normalize_section_spacing(
            wrapped_re.sub(new_section, body, count=1)
        ), "wrapped-header-fallback"

    # Bare form: just `#### Declarations diff` heading + content, no wrap.
    bare_re = re.compile(
        r"####\s*Declarations diff[\s\S]*?(?=^---\s*$|^####\s|\Z)",
        re.MULTILINE,
    )
    m = bare_re.search(body)
    if m:
        return _normalize_section_spacing(
            body[: m.start()] + new_section + "\n" + body[m.end():]
        ), "header-fallback"

    # Nothing matched: append at the end so reviewers still see *something*.
    return body.rstrip() + "\n\n---\n\n" + new_section + "\n", "append"


def splice_warning(body: str, warning_md: str) -> tuple[str, str]:
    """Warning-mode splice: append `warning_md` inside the existing
    `#### Declarations diff` section. Returns `(new_body, mode)`. If
    `WARNING_MARKER` is already present, returns the body unchanged with
    mode suffixed `+already-warned`."""

    marker_re = re.compile(
        re.escape(BEGIN) + r"(.*?)" + re.escape(END),
        re.DOTALL,
    )
    m = marker_re.search(body)
    if m:
        section_inner = m.group(1)
        if WARNING_MARKER in section_inner:
            return body, "markers+already-warned"
        new_inner = section_inner.rstrip() + "\n\n" + warning_md + "\n"
        new_body = body[: m.start()] + BEGIN + new_inner + END + body[m.end():]
        return new_body, "markers"

    # Header fallback: append the warning at the end of the section.
    section_re = re.compile(
        r"(####\s*Declarations diff[\s\S]*?)(?=^---\s*$|^####\s|\Z)",
        re.MULTILINE,
    )
    m = section_re.search(body)
    if m:
        section = m.group(1)
        if WARNING_MARKER in section:
            return body, "header-fallback+already-warned"
        new_section = section.rstrip() + "\n\n" + warning_md + "\n\n"
        new_body = body[: m.start()] + new_section + body[m.end():]
        return new_body, "header-fallback"

    # No section at all: append a minimal one at the end of the comment.
    appended = (
        body.rstrip()
        + "\n\n---\n\n"
        + BEGIN + "\n"
        + "#### Declarations diff\n\n"
        + warning_md + "\n"
        + END + "\n"
    )
    return appended, "append"


def _patch_comment(repo: str, comment_id: int, new_body: str) -> int:
    """PATCH the comment body via `gh api`. Returns the patcher exit code."""
    payload = json.dumps({"body": new_body})
    proc = subprocess.run(
        ["gh", "api", "-X", "PATCH",
         f"repos/{repo}/issues/comments/{comment_id}", "--input", "-"],
        input=payload, text=True, capture_output=True,
    )
    if proc.returncode != 0:
        print(f"updateDeclsDiffSection: PATCH failed: {proc.stderr}", file=sys.stderr)
        return 1
    return 0


def main() -> int:
    repo = os.environ["REPO"]
    head_sha = os.environ["PR_HEAD_SHA"]
    mode = os.environ.get("MODE", "success")

    # PR-number resolution: PR_NUMBER env var > SHA-based lookup.
    # The SHA lookup via `repos/<repo>/commits/<sha>/pulls` misses fork PRs;
    # pass PR_NUMBER directly when known.
    pr_env = os.environ.get("PR_NUMBER", "").strip()
    if pr_env:
        try:
            pr = int(pr_env)
        except ValueError:
            print(f"updateDeclsDiffSection: invalid PR_NUMBER={pr_env!r}", file=sys.stderr)
            return 1
    else:
        try:
            pulls = gh_json(f"repos/{repo}/commits/{head_sha}/pulls")
        except subprocess.CalledProcessError as e:
            print(f"updateDeclsDiffSection: gh api failed: {e.stderr}", file=sys.stderr)
            return 1
        if not pulls:
            print(f"updateDeclsDiffSection: no PR associated with {head_sha} "
                  "(set PR_NUMBER to override); nothing to patch.")
            return 0
        pr = pulls[0]["number"]

    try:
        comments = gh_json(f"repos/{repo}/issues/{pr}/comments")
    except subprocess.CalledProcessError as e:
        print(f"updateDeclsDiffSection: gh api failed: {e.stderr}", file=sys.stderr)
        return 1
    target = next(
        (c for c in comments if c["body"].startswith(PR_SUMMARY_PREFIX)),
        None,
    )
    if target is None:
        print(f"updateDeclsDiffSection: no '{PR_SUMMARY_PREFIX}' comment on PR #{pr}; "
              "pre-build workflow may not have run yet — skipping.")
        return 0

    if mode == "warning":
        default_branch = os.environ.get("DEFAULT_BRANCH", "master")
        warning_md = build_warning(default_branch)
        new_body, splice_mode = splice_warning(target["body"], warning_md)
    else:
        diff_file = os.environ.get("DIFF_FILE", "")
        plus = int(os.environ.get("PLUS", "0"))
        minus = int(os.environ.get("MINUS", "0"))
        diff_text = (
            Path(diff_file).read_text() if diff_file and Path(diff_file).is_file() else ""
        )
        new_section = build_section(plus, minus, diff_text, head_sha)
        new_body, splice_mode = splice(target["body"], new_section)

    if new_body == target["body"]:
        print(f"updateDeclsDiffSection: comment already up-to-date "
              f"(mode={mode}, splice={splice_mode}).")
        return 0

    print(f"updateDeclsDiffSection: patching comment id={target['id']} on PR #{pr} "
          f"(mode={mode}, splice={splice_mode})")
    return _patch_comment(repo, target["id"], new_body)


if __name__ == "__main__":
    sys.exit(main())
