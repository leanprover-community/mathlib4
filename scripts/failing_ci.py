#!/usr/bin/env python3
"""
Script to list open PRs with failing CI checks.
"""

import argparse
import json
import re
import subprocess
import sys
from typing import Optional


def get_open_prs():
    """Get all open PRs for the current user with their CI status."""
    try:
        result = subprocess.run(
            [
                "gh", "pr", "list",
                "--author", "@me",
                "--state", "open",
                "--json", "number,title,url,statusCheckRollup,headRefName,isDraft"
            ],
            capture_output=True,
            text=True,
            check=True
        )
        return json.loads(result.stdout)
    except subprocess.CalledProcessError as e:
        print(f"Error running gh command: {e}", file=sys.stderr)
        print(f"stderr: {e.stderr}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error parsing JSON: {e}", file=sys.stderr)
        sys.exit(1)


def has_failing_checks(pr):
    """Check if a PR has any failing CI checks."""
    if not pr.get("statusCheckRollup"):
        return False

    for check in pr["statusCheckRollup"]:
        conclusion = check.get("conclusion", "")
        # Consider FAILURE or ACTION_REQUIRED as failing
        if conclusion in ["FAILURE", "ACTION_REQUIRED"]:
            return True

    return False


def get_failing_checks(pr):
    """Get list of failing check names for a PR."""
    failing = []
    if not pr.get("statusCheckRollup"):
        return failing

    for check in pr["statusCheckRollup"]:
        conclusion = check.get("conclusion", "")
        if conclusion in ["FAILURE", "ACTION_REQUIRED"]:
            name = check.get("name", "Unknown")
            workflow = check.get("workflowName", "")
            details_url = check.get("detailsUrl", "")
            failing.append((name, workflow, details_url))

    return failing


def get_job_id_from_url(url: str) -> Optional[str]:
    """Extract job ID from GitHub Actions URL."""
    match = re.search(r'/job/(\d+)', url)
    return match.group(1) if match else None


def get_job_logs(job_id: str) -> Optional[str]:
    """Fetch logs for a specific job."""
    try:
        result = subprocess.run(
            [
                "gh", "api",
                f"repos/leanprover-community/mathlib4/actions/jobs/{job_id}/logs"
            ],
            capture_output=True,
            text=True,
            check=False
        )
        return result.stdout + result.stderr
    except Exception:
        return None


def extract_error_snippet(logs: str, max_lines: int = 8) -> Optional[str]:
    """Extract a concise error snippet from build logs."""
    if not logs:
        return None

    lines = logs.split('\n')
    error_snippets = []
    i = 0

    while i < len(lines):
        line = lines[i]

        if '##[error]error:' in line:
            match = re.search(r'error: ([^:]+):(\d+):(\d+): (.+)', line)
            if match:
                file_path = match.group(1).replace('Mathlib/', '')
                line_num = match.group(2)
                col_num = match.group(3)
                error_type = match.group(4)

                context_lines = [f"{file_path}:{line_num}:{col_num}: {error_type}"]
                j = i + 1
                collected = 0

                while j < len(lines) and collected < (max_lines - 1):
                    next_line = lines[j]
                    if '##[error]' in next_line or '✔ [' in next_line or '✖ [' in next_line:
                        break
                    clean_line = re.sub(r'^\d{4}-\d{2}-\d{2}T[\d:.]+Z\s+', '', next_line)
                    clean_line = re.sub(r'\x1b\[[0-9;]*m', '', clean_line)
                    if clean_line.strip():
                        context_lines.append('  ' + clean_line)
                        collected += 1
                    j += 1

                return '\n'.join(context_lines)

        i += 1

    return None


def main():
    parser = argparse.ArgumentParser(
        description="List open PRs with failing CI checks, or check a specific PR"
    )
    parser.add_argument(
        "pr_number",
        nargs="?",
        type=int,
        help="Optional: Check a specific PR number instead of listing all failing PRs"
    )
    parser.add_argument(
        "--include-drafts",
        action="store_true",
        help="Include draft PRs in the results (default: exclude drafts)"
    )
    parser.add_argument(
        "--no-errors",
        action="store_true",
        help="Don't fetch and display error snippets from CI logs (default: show errors)"
    )
    args = parser.parse_args()

    # If specific PR number is provided, check only that PR
    if args.pr_number:
        print(f"Checking PR #{args.pr_number}...")
        prs = get_open_prs()
        target_pr = next((pr for pr in prs if pr['number'] == args.pr_number), None)

        if not target_pr:
            print(f"\n✗ PR #{args.pr_number} not found in your open PRs")
            return

        failing_prs = [target_pr] if has_failing_checks(target_pr) else []

        if not failing_prs:
            print(f"\n✓ PR #{args.pr_number} has no failing CI checks!")
            return

        print(f"\n✗ PR #{args.pr_number} has failing CI:\n")
    else:
        # List all failing PRs
        print("Fetching open PRs...")
        prs = get_open_prs()

        # Filter for PRs with failing checks
        failing_prs = [pr for pr in prs if has_failing_checks(pr)]

        # Filter out drafts unless --include-drafts is specified
        if not args.include_drafts:
            failing_prs = [pr for pr in failing_prs if not pr.get("isDraft", False)]

        if not failing_prs:
            draft_msg = " (excluding drafts)" if not args.include_drafts else ""
            print(f"\n✓ No open PRs with failing CI checks{draft_msg}!")
            return

        draft_msg = " (including drafts)" if args.include_drafts else " (excluding drafts)"
        print(f"\n✗ Found {len(failing_prs)} PR(s) with failing CI{draft_msg}:\n")

    for pr in failing_prs:
        draft_indicator = " [DRAFT]" if pr.get("isDraft", False) else ""
        print(f"#{pr['number']}: {pr['title']}{draft_indicator}")
        print(f"  Branch: {pr['headRefName']}")
        print(f"  URL: {pr['url']}")

        failing_checks = get_failing_checks(pr)
        print(f"  Failing checks ({len(failing_checks)}):")
        for check_name, workflow, details_url in failing_checks:
            if workflow and workflow != check_name:
                print(f"    - {check_name} ({workflow})")
            else:
                print(f"    - {check_name}")

        # Fetch and display error snippet (unless --no-errors is specified)
        if not args.no_errors and failing_checks:
            _, _, first_failing_url = failing_checks[0]
            job_id = get_job_id_from_url(first_failing_url)
            if job_id:
                print(f"\n  Fetching error details...")
                logs = get_job_logs(job_id)
                if logs:
                    snippet = extract_error_snippet(logs)
                    if snippet:
                        print(f"  Error snippet:")
                        for line in snippet.split('\n'):
                            print(f"    {line}")
                    else:
                        print(f"  (Could not extract error snippet)")
                else:
                    print(f"  (Logs unavailable or expired)")

        print()


if __name__ == "__main__":
    main()
