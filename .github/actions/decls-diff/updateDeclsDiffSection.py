#!/usr/bin/env python3
"""Patch the `#### Declarations diff` section of an existing "### PR summary"
comment with a Lean-aware diff produced by the decls-diff action.

This script is intentionally policy-light: the *action* produces the data
(plus/minus counts, the diff file); *this* script knows how to splice it into
the existing comment without disturbing the rest of the summary.

Inputs are read from environment variables:
    GH_TOKEN       — passed through to the `gh` CLI for auth
    REPO           — `owner/repo`
    PR_HEAD_SHA    — head SHA of the PR (the workflow_run head_sha)
    MODE           — `success` (default) or `warning`
    DIFF_FILE      — (success mode) path to the +/- diff file from the dumper
    PLUS, MINUS    — (success mode) counts of `+NAME` / `-NAME` lines
    DEFAULT_BRANCH — (warning mode, optional) shown in the rebase suggestion
                     (defaults to `master`)

Behaviour:

  1. Resolve the PR number from PR_HEAD_SHA via `gh api /commits/<sha>/pulls`.
     If no PR is associated (e.g. push to a branch without a PR), exit 0
     silently — there's nothing to patch.

  2. Find the comment whose body starts with `### PR summary` (the convention
     `update_PR_comment.sh` uses). If no such comment exists yet — the
     pre-build `PR_summary` workflow may not have finished — exit 0 silently.

  3. Mode `success`:
       Replace text between `<!-- DECLS_DIFF_BEGIN -->` and
       `<!-- DECLS_DIFF_END -->` (or fall back to a header-based detection of
       the `#### Declarations diff` block) with a freshly-built Lean-aware
       section, including the post-build stamp.

     Mode `warning`:
       Leave the existing section's body untouched and append a single
       blockquote that explains why no Lean-aware diff was produced and asks
       the PR author to merge the default branch. Idempotent via the
       `WARNING_MARKER` sentinel.

  4. PATCH the comment via `gh api -X PATCH ... --input -`.

Exit codes:
    0 — patched successfully, or skipped because there was nothing to patch
    1 — a non-recoverable error (gh CLI failure, malformed env, ...)
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
# Matches `PR_summary.yml`'s heuristic for `declarations_diff.sh`: wrap the
# whole section in `<details>` once the rendered body exceeds this many
# newlines. Kept identical so reviewers see the same collapse threshold for
# the pre-build and post-build versions.
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
    """Render the Lean-aware `#### Declarations diff` section, including the
    sentinel markers and the post-build stamp.

    Mirrors the collapse heuristic from `.github/workflows/PR_summary.yml`:
    when the rendered body has more than `DETAILS_LINE_THRESHOLD` newlines,
    the whole section is wrapped in `<details><summary>#### Declarations
    diff</summary>…</details>`; otherwise the heading and body render
    inline."""
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
    """Render a `<details>` block whose `<summary>` is just the one-line
    status (`⚠️ **Lean-aware diff unavailable**`) and whose body holds the
    explanation + rebase suggestion. Lives inside the existing
    `#### Declarations diff` section without disturbing the pre-build (regex)
    content above it. The unique `WARNING_MARKER` HTML comment makes the
    patcher idempotent on re-runs."""
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


def splice(body: str, new_section: str) -> tuple[str, str]:
    """Success-mode splice: replace the entire Declarations-diff section.

    Returns `(new_body, mode)` where `mode` is one of `markers`,
    `header-fallback`, `append`."""

    marker_re = re.compile(
        re.escape(BEGIN) + r".*?" + re.escape(END),
        re.DOTALL,
    )
    if marker_re.search(body):
        return marker_re.sub(new_section, body, count=1), "markers"

    # Fallback: match the `#### Declarations diff` heading and consume until
    # the next horizontal rule, the next `####`, or end-of-body.
    section_re = re.compile(
        r"####\s*Declarations diff[\s\S]*?(?=^---\s*$|^####\s|\Z)",
        re.MULTILINE,
    )
    m = section_re.search(body)
    if m:
        return body[: m.start()] + new_section + "\n" + body[m.end():], "header-fallback"

    # Nothing matched: append at the end so reviewers still see *something*.
    return body.rstrip() + "\n\n---\n\n" + new_section + "\n", "append"


def splice_warning(body: str, warning_md: str) -> tuple[str, str]:
    """Warning-mode splice: append `warning_md` inside the existing
    `#### Declarations diff` section without disturbing anything else.

    Returns `(new_body, mode)`. If `WARNING_MARKER` is already present in
    the section, the body is returned unchanged with mode suffixed
    `+already-warned` so the caller can skip the PATCH."""

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
    # The SHA lookup uses `repos/<repo>/commits/<sha>/pulls`, which only
    # returns PRs whose head branch lives in this repo — so it MISSES fork
    # PRs (the common case for Mathlib). Callers that know the PR number
    # (e.g. via `inputs.pr_number` on `decls-diff.yml`) should pass it
    # via PR_NUMBER to bypass the unreliable lookup.
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
