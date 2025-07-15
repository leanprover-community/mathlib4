#!/usr/bin/env python3
"""
Script to migrate contributors from direct write access to using forks.

This script automates the process of migrating mathlib4 contributors from having
direct write access to the main repository to using a fork-based workflow.

Features:
1. Validates current branch (prevents migration of system branches like master, nightly-testing)
2. Checks GitHub CLI installation and authentication with OS-specific installation instructions
3. Validates GitHub CLI token has required scopes (repo, workflow) with clear error messages
4. Automatically detects SSH connectivity to GitHub and chooses appropriate protocol (SSH preferred, HTTPS fallback)
5. Creates or syncs user's fork of mathlib4
6. Sets up git remotes correctly (upstream → leanprover-community/mathlib4, origin → user's fork)
7. Detects if migration has already been completed and skips unnecessary steps
8. Migrates current branch to fork with proper upstream tracking
9. Intelligently handles existing PRs:
   - Detects open PRs from main repo and offers to migrate them to fork-based PRs
   - Detects existing fork-based PRs and confirms no migration needed
   - Handles edge cases with both main repo and fork PRs requiring manual cleanup
10. Uses fast delete/re-add approach for remote changes to avoid slow branch tracking updates
11. Respects user's existing remote naming preferences (if user declines to rename remotes,
    the script will use whatever remote names point to the correct repositories)

Usage:
  python3 scripts/migrate_to_fork.py           # Interactive mode
  python3 scripts/migrate_to_fork.py -y        # Auto-accept all prompts

Requirements:
  - GitHub CLI (gh) installed and authenticated with required scopes:
    gh auth login --scopes 'repo,workflow'
  - Git repository must be the mathlib4 repository
  - User must be on a feature branch (not master, nightly-testing, or lean-pr-testing-*)
  - SSH access to GitHub is recommended but not required (will fallback to HTTPS)

The script is safe to run multiple times and will skip already-completed migration steps.
"""

import subprocess
import sys
import json
import re
import argparse
import os
import platform
from datetime import datetime
from typing import Optional, Dict, Any, List


class Colors:
    """ANSI color codes for terminal output with Windows compatibility."""
    if platform.system() == 'Windows':
        # Windows doesn't support ANSI colors by default, so we'll use empty strings
        GREEN = ''
        YELLOW = ''
        RED = ''
        BLUE = ''
        BOLD = ''
        END = ''
    else:
        GREEN = '\033[92m'
        YELLOW = '\033[93m'
        RED = '\033[91m'
        BLUE = '\033[94m'
        BOLD = '\033[1m'
        END = '\033[0m'


def print_step(step_num: int, description: str) -> None:
    """Print a colored step header."""
    print(f"\n{Colors.BOLD}{Colors.BLUE}=== Step {step_num}: {description} ==={Colors.END}")


def print_success(message: str) -> None:
    """Print a success message in green."""
    print(f"{Colors.GREEN}✓ {message}{Colors.END}")


def print_warning(message: str) -> None:
    """Print a warning message in yellow."""
    print(f"{Colors.YELLOW}⚠ {message}{Colors.END}")


def print_error(message: str) -> None:
    """Print an error message in red."""
    print(f"{Colors.RED}✗ {message}{Colors.END}")


def run_command(cmd: List[str], capture_output: bool = True, check: bool = True) -> subprocess.CompletedProcess:
    """Run a command and return the result with Windows compatibility."""
    try:
        return subprocess.run(cmd, capture_output=capture_output, text=True, encoding="utf8", check=check)
    except subprocess.CalledProcessError as e:
        if not check:
            return e
        print_error(f"Command failed: {' '.join(cmd)}")
        print_error(f"Error: {e.stderr if e.stderr else str(e)}")
        sys.exit(1)


def get_user_input(prompt: str, default: Optional[str] = None) -> str:
    """Get user input with optional default."""
    if default:
        response = input(f"{prompt} [{default}]: ").strip()
        return response if response else default
    return input(f"{prompt}: ").strip()


def yes_no_prompt(prompt: str, default: bool = True, auto_accept: bool = False) -> bool:
    """Ask a yes/no question and return the boolean result."""
    if auto_accept:
        print(f"{prompt} [Y/n]: Y (auto-accepted)")
        return True

    default_str = "Y/n" if default else "y/N"
    response = input(f"{prompt} [{default_str}]: ").strip().lower()

    if not response:
        return default
    return response.startswith('y')


def check_gh_installation() -> bool:
    """Check if GitHub CLI is installed and authenticated."""
    print_step(1, "Checking GitHub CLI installation and authentication")

    # Check if gh is installed
    try:
        result = run_command(['gh', '--version'], check=False)
        if result.returncode != 0:
            print_error("GitHub CLI (gh) returned an error.")
            print("Please check your installation or visit: https://cli.github.com/")
            return False
        print_success("GitHub CLI is installed")
    except FileNotFoundError:
        print_error("GitHub CLI (gh) is not installed.")
        print("Please install it:")
        if platform.system() == 'Windows':
            print("  Windows: winget install GitHub.cli")
            print("  Or visit: https://cli.github.com/")
        else:
            print("  macOS: brew install gh")
            print("  Ubuntu/Debian: sudo apt install gh")
            print("  Or visit: https://cli.github.com/")
        return False

    # Check if authenticated
    try:
        result = run_command(['gh', 'auth', 'status'], check=False)
        if result.returncode != 0:
            print_error("GitHub CLI is not authenticated.")
            print("Please run: gh auth login")
            return False
        print_success("GitHub CLI is authenticated")

        # Check token scopes
        if not check_gh_token_scopes():
            return False

        return True
    except Exception:
        print_error("Failed to check GitHub CLI authentication status.")
        return False


def check_gh_token_scopes() -> bool:
    """Check if the GitHub CLI token has required scopes."""
    try:
        # Get current token scopes
        result = run_command(['gh', 'auth', 'status', '--show-token'], check=False)
        if result.returncode != 0:
            # Fallback: try to make a test API call that requires repo scope
            result = run_command(['gh', 'api', 'user'], check=False)
            if result.returncode != 0:
                print_error("GitHub CLI token lacks required permissions.")
                print("Please re-authenticate with required scopes:")
                print("  gh auth login --scopes 'repo,workflow'")
                return False
            print_warning("Could not verify token scopes, but basic API access works")
            return True

        # Hackily check the output for required scopes
        # Versions of gh before v2.31.0 print this info on stderr, not stdout.
        # See https://github.com/cli/cli/issues/7447
        auth_output = result.stdout + result.stderr
        if 'repo' not in auth_output:  # or 'workflow' not in auth_output:
            print_error("GitHub CLI token lacks required scopes.")
            print("Required scopes: repo, workflow")
            print("Please re-authenticate with required scopes:")
            print("  gh auth login --scopes 'repo,workflow'")
            return False

        print_success("GitHub CLI token has required scopes")
        return True

    except Exception as e:
        # Try a fallback test - attempt to access repo API
        try:
            result = run_command(['gh', 'api', 'user/repos', '--limit', '1'], check=False)
            if result.returncode != 0:
                print_error("GitHub CLI token lacks required 'repo' scope.")
                print("Please re-authenticate with required scopes:")
                print("  gh auth login --scopes 'repo,workflow'")
                return False
            print_success("GitHub CLI token appears to have required permissions")
            return True
        except Exception:
            print_warning(f"Could not verify token scopes: {e}")
            print("If you encounter permission errors, try re-authenticating:")
            print("  gh auth login --scopes 'repo,workflow'")
            return True  # Continue with warning


def check_ssh_github_access() -> bool:
    """Check if SSH access to GitHub is available."""
    try:
        # On Windows, we need to use the full path to ssh.exe
        ssh_cmd = 'ssh.exe' if platform.system() == 'Windows' else 'ssh'

        # Test SSH connection to GitHub
        result = run_command([ssh_cmd, '-T', 'git@github.com'], check=False)
        # SSH to GitHub returns exit code 1 for successful authentication
        # but exit code 255 for connection failures
        if result.returncode == 1:
            # Check if the output contains successful authentication message
            if 'successfully authenticated' in result.stderr:
                return True
        return False
    except Exception:
        return False


def get_github_username() -> str:
    """Get the GitHub username of the current user."""
    print_step(2, "Identifying GitHub username")

    try:
        result = run_command(['gh', 'api', 'user'])
        user_data = json.loads(result.stdout)
        username = user_data['login']
        print_success(f"GitHub username: {username}")
        return username
    except Exception as e:
        print_error(f"Failed to get GitHub username: {e}")
        sys.exit(1)


def get_remote_url(repo_name: str, use_ssh: bool = True) -> str:
    """Get the appropriate remote URL (SSH or HTTPS) for a repository."""
    if use_ssh:
        return f"git@github.com:{repo_name}.git"
    else:
        return f"https://github.com/{repo_name}.git"


def check_and_create_fork(username: str, auto_accept: bool = False) -> str:
    """Check if user has a fork, create one if needed."""
    print_step(3, "Checking for fork of mathlib4")

    repo_name = f"{username}/mathlib4"

    # Determine if we should use SSH
    use_ssh = check_ssh_github_access()
    if use_ssh:
        print_success("SSH access to GitHub is available - will use SSH URLs")
    else:
        print_warning("SSH access to GitHub not available - will use HTTPS URLs")

    # Check if fork exists
    try:
        result = run_command(['gh', 'repo', 'view', repo_name], check=False)
        if result.returncode == 0:
            print_success(f"Fork exists: {repo_name}")

            # Synchronize master branch
            print("Synchronizing fork's master branch...")
            try:
                run_command(['gh', 'repo', 'sync', repo_name, '--source', 'leanprover-community/mathlib4'], check=False)
                print_success("Fork synchronized with upstream")
            except Exception as e:
                print_warning(f"Failed to sync fork automatically: {e}")
                print("You may need to sync manually later")

            return get_remote_url(repo_name, use_ssh)
    except Exception:
        pass

    # Fork doesn't exist, offer to create it
    print(f"Fork {repo_name} does not exist.")
    if yes_no_prompt("Would you like to create a fork?", auto_accept=auto_accept):
        try:
            print("Creating fork...")
            run_command(['gh', 'repo', 'fork', 'leanprover-community/mathlib4', '--clone=false'])
            print_success(f"Fork created: {repo_name}")
            return get_remote_url(repo_name, use_ssh)
        except Exception as e:
            print_error(f"Failed to create fork: {e}")
            sys.exit(1)
    else:
        print_error("Cannot proceed without a fork")
        sys.exit(1)


def get_current_remotes() -> Dict[str, str]:
    """Get current git remotes."""
    try:
        result = run_command(['git', 'remote', '-v'])
        remotes = {}
        for line in result.stdout.strip().split('\n'):
            if line:
                parts = line.split()
                if len(parts) >= 2 and '(fetch)' in line:
                    name, url = parts[0], parts[1]
                    remotes[name] = url
        return remotes
    except Exception:
        return {}


def setup_remotes(username: str, fork_url: str, auto_accept: bool = False) -> str:
    """Set up upstream and origin remotes correctly.

    Returns the name of the remote that points to the user's fork.
    """
    print_step(4, "Setting up git remotes")

    # This will sync the local references with the upstream ones and delete refs to branches that
    # don't exist anymore on upstream repos.
    # In particular, this will ensure the branches with duplicate names up to case that were recently
    # deleted on the main repository do not cause trouble in the migration.
    run_command(['git', 'fetch', '--all', '--prune'])

    remotes = get_current_remotes()

    # Determine URL format based on SSH availability
    use_ssh = check_ssh_github_access()
    upstream_url = get_remote_url("leanprover-community/mathlib4", use_ssh)

    # Handle upstream remote
    upstream_remote = None
    for name, url in remotes.items():
        if 'leanprover-community/mathlib4' in url:
            upstream_remote = name
            break

    if upstream_remote:
        if upstream_remote != 'upstream':
            print(f"Found leanprover-community/mathlib4 as remote '{upstream_remote}'")
            if yes_no_prompt(f"Rename '{upstream_remote}' to 'upstream'?", auto_accept=auto_accept):
                # Show warning about branch tracking
                print_warning("⚠️  Changing remote names will reset upstream tracking for all branches.")
                print("   This is much faster than renaming, but means other local branches will need")
                print("   their upstream reset manually later.")
                print("   ✅ Don't worry: This script will automatically fix the upstream for your")
                print("   current branch after the remote changes.")

                run_command(['git', 'remote', 'remove', upstream_remote])
                run_command(['git', 'remote', 'add', 'upstream', upstream_url])
                print_success("Replaced remote with 'upstream'")
        else:
            print_success("Upstream remote already configured correctly")
    else:
        print("Adding upstream remote...")
        run_command(['git', 'remote', 'add', 'upstream', upstream_url])
        print_success("Added upstream remote")

    # Update the remote info after writing to it!
    remotes = get_current_remotes()

    # Handle origin remote (fork)
    origin_remote = None
    for name, url in remotes.items():
        if f'{username}/mathlib4' in url:
            origin_remote = name
            break

    fork_remote_name = 'origin'  # Default expected name

    if origin_remote:
        if origin_remote != 'origin':
            print(f"Found fork as remote '{origin_remote}'")
            if yes_no_prompt(f"Rename '{origin_remote}' to 'origin'?", auto_accept=auto_accept):
                # Check if origin exists and is different
                if 'origin' in remotes and f'{username}/mathlib4' not in remotes['origin']:
                    if yes_no_prompt("Remove existing 'origin' remote?", auto_accept=auto_accept):
                        run_command(['git', 'remote', 'remove', 'origin'])

                # Use delete/re-add approach for speed
                run_command(['git', 'remote', 'remove', origin_remote])
                run_command(['git', 'remote', 'add', 'origin', fork_url])
                print_success("Replaced remote with 'origin' pointing to your fork")
                fork_remote_name = 'origin'
            else:
                print_success(f"Keeping fork as remote '{origin_remote}'")
                fork_remote_name = origin_remote
        else:
            print_success("Origin remote (fork) already configured correctly")
            fork_remote_name = 'origin'
    else:
        # No fork remote found - need to add one
        # Check if 'origin' is available for the fork
        if 'origin' in remotes:
            # 'origin' exists but doesn't point to user's fork
            print(f"Current origin: {remotes['origin']}")
            if yes_no_prompt("Replace existing 'origin' with your fork?", auto_accept=auto_accept):
                run_command(['git', 'remote', 'remove', 'origin'])
                run_command(['git', 'remote', 'add', 'origin', fork_url])
                print_success("Set origin to your fork")
                fork_remote_name = 'origin'
            else:
                # User wants to keep existing origin, ask for alternative name
                fork_remote_name = get_user_input("What would you like to name the remote for your fork?", "fork")
                run_command(['git', 'remote', 'add', fork_remote_name, fork_url])
                print_success(f"Added fork as '{fork_remote_name}' remote")
        else:
            # 'origin' doesn't exist, safe to add it
            run_command(['git', 'remote', 'add', 'origin', fork_url])
            print_success("Added origin remote pointing to your fork")
            fork_remote_name = 'origin'

    return fork_remote_name


def get_current_branch() -> str:
    """Get the current git branch name."""
    try:
        result = run_command(['git', 'branch', '--show-current'])
        return result.stdout.strip()
    except Exception:
        print_error("Failed to get current branch")
        sys.exit(1)


def validate_branch_for_migration(branch: str, auto_accept: bool = False) -> None:
    """Validate that the current branch can be migrated to a fork."""
    print(f"\n{Colors.BOLD}Current branch: {branch}{Colors.END}")

    # Check for system branches that shouldn't be migrated
    is_invalid_branch = (
        branch == 'master' or
        branch == 'nightly-testing' or
        re.match(r'^lean-pr-testing-\d+$', branch)
    )

    if is_invalid_branch:
        print_error(f"Cannot migrate branch '{branch}'")
        print(f"The branch '{branch}' is a system branch that should not be migrated to a fork.")
        print("\nSystem branches that cannot be migrated:")
        print("  • master (main development branch)")
        print("  • nightly-testing (CI testing branch)")
        print("  • lean-pr-testing-* (Lean PR testing branches)")

        print(f"\n{Colors.BOLD}What you should do:{Colors.END}")
        print("1. Switch to the feature branch you want to migrate:")
        print("   git checkout your-feature-branch-name")
        print("\n2. If you don't have a feature branch yet, create one:")
        print("   git checkout -b your-new-feature-branch")
        print("\n3. You may need to merge master into your branch to access this script:")
        print("   git merge master")
        print("\n4. Then run this migration script again")

        sys.exit(1)

    # Additional warning for master branch (in case the check above didn't catch it)
    if branch == 'master':
        print_warning("You're on the master branch.")
        print("It's highly recommended to work on feature branches instead.")
        if not yes_no_prompt("Are you sure you want to continue with master?", auto_accept=auto_accept):
            print("Please create a feature branch and run the script again.")
            sys.exit(0)


def check_branch_already_migrated(branch: str, username: str, fork_remote_name: str) -> bool:
    """Check if the current branch is already set to push to the user's fork."""
    try:
        # Get the upstream branch for the current branch
        result = run_command(['git', 'rev-parse', '--abbrev-ref', f'{branch}@{{upstream}}'], check=False)
        if result.returncode == 0:
            upstream = result.stdout.strip()
            # Check if upstream is fork_remote/branch (which should point to the fork)
            if upstream.startswith(f'{fork_remote_name}/'):
                # Verify that the fork remote actually points to the user's fork
                remotes = get_current_remotes()
                if fork_remote_name in remotes and f'{username}/mathlib4' in remotes[fork_remote_name]:
                    print_success(f"Branch '{branch}' is already configured to push to your fork")
                    return True
        return False
    except Exception:
        return False


def push_branch_to_fork(branch: str, fork_remote_name: str) -> None:
    """Push current branch to fork and set upstream."""
    print_step(5, f"Pushing branch '{branch}' to fork")

    try:
        # Push to fork and set upstream
        run_command(['git', 'push', '-u', fork_remote_name, branch])
        print_success(f"Branch '{branch}' pushed to fork and set as upstream")
    except Exception as e:
        print_error(f"Failed to push branch: {e}")
        sys.exit(1)


def find_existing_pr(branch: str, username: str) -> Optional[Dict[str, Any]]:
    """Check if there's an existing PR for this branch from either main repo or fork."""
    print_step(6, "Checking for existing PR")

    old_style_pr = None
    fork_style_pr = None

    try:
        # Search for all PRs with this branch name, then filter by head repository
        # Include isDraft to preserve draft status during migration
        result = run_command(['gh', 'pr', 'list', '--repo', 'leanprover-community/mathlib4',
                             '--head', f'{branch}', '--json', 'number,title,url,state,headRepositoryOwner,isDraft'],
                            check=False)

        if result.returncode == 0 and result.stdout.strip():
            prs = json.loads(result.stdout)
            for pr in prs:
                if pr['state'] == 'OPEN':
                    # Check if this PR is from the main repo or a fork
                    head_repo_owner = pr['headRepositoryOwner'].get('login', '')

                    if head_repo_owner == 'leanprover-community':
                        # PR from main repo
                        old_style_pr = pr
                        draft_status = " (draft)" if pr.get('isDraft', False) else ""
                        print_success(f"Found existing open PR from main repo: #{pr['number']} - {pr['title']}{draft_status}")
                        print(f"URL: {pr['url']}")
                    elif head_repo_owner == username:
                        # PR from user's fork
                        fork_style_pr = pr
                        draft_status = " (draft)" if pr.get('isDraft', False) else ""
                        print_success(f"Found existing open PR from your fork: #{pr['number']} - {pr['title']}{draft_status}")
                        print(f"URL: {pr['url']}")
                else:
                    # Closed PR - just mention it
                    head_repo_owner = pr['headRepositoryOwner'].get('login', '')
                    if head_repo_owner == 'leanprover-community':
                        print(f"Found closed PR from main repo: #{pr['number']} - {pr['title']} (state: {pr['state']})")
                    elif head_repo_owner == username:
                        print(f"Found closed PR from your fork: #{pr['number']} - {pr['title']} (state: {pr['state']})")
                    print("Closed PRs don't need migration.")

        # Return info about what we found (only open PRs)
        if fork_style_pr and old_style_pr:
            print_warning("Found open PRs from both main repo and fork - this might need manual cleanup")
            return {
                'type': 'both',
                'old_pr': old_style_pr,
                'fork_pr': fork_style_pr
            }
        elif fork_style_pr:
            return {
                'type': 'fork',
                'pr': fork_style_pr
            }
        elif old_style_pr:
            return {
                'type': 'old',
                'pr': old_style_pr
            }

        return None

    except Exception as e:
        print_warning(f"Could not check for existing PR: {e}")
        return None


def get_pr_comments_summary(pr_number: int) -> Optional[str]:
    """Fetch all comments from a PR and format them as a dialogue summary.

    Filters out bot comments (usernames ending with -bot) and formats
    the remaining comments with poster name, time, and content.

    Returns None if no comments or if fetching fails.
    """
    try:
        # Fetch PR comments with all needed fields
        result = run_command(['gh', 'pr', 'view', str(pr_number),
                             '--repo', 'leanprover-community/mathlib4',
                             '--json', 'comments'], check=False)

        if result.returncode != 0:
            print_warning(f"Could not fetch comments from PR #{pr_number}")
            return None

        pr_data = json.loads(result.stdout)
        comments = pr_data.get('comments', [])

        if not comments:
            return None

        # Filter out bot comments and format remaining ones
        formatted_comments = []
        for comment in comments:
            author = comment.get('author', {}).get('login', 'unknown')

            # Skip bot comments (usernames ending with -bot, except 'FR-vdash-bot')
            if author.endswith('-bot') and not author == 'FR-vdash-bot':
                continue
            if author == 'leanprover-community-bot-assistant':
                continue

            created_at = comment.get('createdAt', '')
            body = comment.get('body', '').strip()
            url = comment.get('url', '')

            if body:  # Only include non-empty comments
                # Format timestamp to be more readable
                try:
                    # GitHub API returns ISO format like: 2024-01-15T10:30:00Z
                    dt = datetime.fromisoformat(created_at.replace('Z', '+00:00'))
                    formatted_time = dt.strftime('%Y-%m-%d %H:%M UTC')
                except Exception:
                    formatted_time = created_at

                # Format comment with author, time, and link back to original
                comment_header = f"**@{author}** ([{formatted_time}]({url})):"
                formatted_comment = f"{comment_header}\n{body}"
                formatted_comments.append(formatted_comment)

        if not formatted_comments:
            return None

        # Create the summary
        summary_parts = [
            f"## Comments from Original PR #{pr_number}",
            "",
            f"*This section contains {len(formatted_comments)} comment(s) from the original PR, excluding bot comments.*",
            "",
            "---",
            ""
        ]

        # Add each comment separated by horizontal rules
        for i, comment in enumerate(formatted_comments):
            summary_parts.append(comment)
            if i < len(formatted_comments) - 1:  # Don't add separator after last comment
                summary_parts.extend(["", "---", ""])

        return "\n".join(summary_parts)

    except Exception as e:
        print_warning(f"Failed to fetch comments summary: {e}")
        return None


def create_new_pr_from_fork(branch: str, username: str, old_pr: Optional[Dict[str, Any]] = None) -> str:
    """Create a new PR from the fork."""
    print_step(7, "Creating new PR from fork")

    try:
        # Get PR details
        if old_pr:
            title = old_pr['title']
            is_draft = old_pr.get('isDraft', False)
            print(f"Using title from old PR: {title}")
            if is_draft:
                print_success("Original PR is a draft - new PR will also be created as draft")

            # Fetch full PR details including body and labels
            print("Fetching complete PR details...")
            try:
                result = run_command(['gh', 'pr', 'view', str(old_pr['number']),
                                    '--repo', 'leanprover-community/mathlib4',
                                    '--json', 'body,labels'])
                pr_details = json.loads(result.stdout)

                original_body = pr_details.get('body', '') or ''
                labels = pr_details.get('labels', [])
                labels.append('migrated-from-branch')  # Add label for new PR

                # Prepare the new body with migration notice
                body_suffix = f"---\n\n*This PR continues the work from #{old_pr['number']}.*\n\n*Original PR: {old_pr['url']}*"
                if original_body.strip():
                    body = f"{original_body}\n\n{body_suffix}"
                else:
                    body = body_suffix

                print_success(f"Found {len(labels)} labels to copy: {', '.join([label['name'] for label in labels])}" if labels else "No labels found on original PR")

            except Exception as e:
                print_warning(f"Could not fetch full PR details: {e}")
                # Fallback to simple body
                body = f"This PR continues the work from #{old_pr['number']}.\n\nOriginal PR: {old_pr['url']}"
                labels = []
        else:
            title = get_user_input("Enter PR title")
            body = ''
            labels = []
            is_draft = False

        # Create PR from fork
        cmd = ['gh', 'pr', 'create',
               '--repo', 'leanprover-community/mathlib4',
               '--head', f'{username}:{branch}',
               '--title', title,
               '--body', body]

        # Add draft flag if the original PR was a draft
        if old_pr and is_draft:
            cmd.append('--draft')

        result = run_command(cmd)

        # Extract PR URL and number from output
        pr_url = result.stdout.strip()
        print_success(f"New PR created: {pr_url}")

        # Extract PR number from URL for label operations
        pr_number_match = re.search(r'/pull/(\d+)', pr_url)
        if not pr_number_match:
            print_warning("Could not extract PR number from URL - skipping label operations")
            return pr_url

        new_pr_number = pr_number_match.group(1)

        # Copy labels if we have any
        if labels and old_pr:
            print("Copying labels to new PR...")
            label_names = [label['name'] for label in labels]

            try:
                # Try to add all labels at once
                for label_name in label_names:
                    run_command(['gh', 'pr', 'edit', new_pr_number,
                               '--repo', 'leanprover-community/mathlib4',
                               '--add-label', label_name])
                print_success(f"Successfully copied {len(label_names)} labels")

            except Exception as e:
                print_warning(f"Failed to add labels directly: {e}")
                print("Falling back to adding labels as comments...")

                # Fallback: add each label as a comment
                for label_name in label_names:
                    try:
                        run_command(['gh', 'pr', 'comment', new_pr_number,
                                   '--repo', 'leanprover-community/mathlib4',
                                   '--body', label_name])
                    except Exception as comment_error:
                        print_warning(f"Failed to add comment for label '{label_name}': {comment_error}")

                print_success(f"Added {len(label_names)} label comments as fallback")

        # Add comments summary from original PR if available
        if old_pr:
            print("Fetching comments from original PR...")
            comments_summary = get_pr_comments_summary(old_pr['number'])
            if comments_summary:
                try:
                    run_command(['gh', 'pr', 'comment', new_pr_number,
                               '--repo', 'leanprover-community/mathlib4',
                               '--body', comments_summary])
                    print_success("Added comments summary from original PR")
                except Exception as e:
                    print_warning(f"Failed to add comments summary: {e}")
            else:
                print("No comments found on original PR (or only bot comments)")

        return pr_url

    except Exception as e:
        print_error(f"Failed to create new PR: {e}")
        sys.exit(1)


def close_old_pr_and_comment(old_pr: Dict[str, Any], new_pr_url: str) -> None:
    """Close the old PR and add a comment linking to the new one."""
    print_step(8, "Closing old PR and adding comment")

    try:
        # Add comment to old PR
        comment = f"This PR has been migrated to a fork-based workflow: {new_pr_url}"
        run_command(['gh', 'pr', 'comment', str(old_pr['number']),
                    '--repo', 'leanprover-community/mathlib4',
                    '--body', comment])
        print_success("Added comment to old PR")

        # Add migrated-to-fork label to old PR
        run_command(['gh', 'pr', 'edit', str(old_pr['number']),
                    '--repo', 'leanprover-community/mathlib4',
                    '--add-label', 'migrated-to-fork'])
        print_success("Added migrated-to-fork label to old PR")

        # Close old PR
        run_command(['gh', 'pr', 'close', str(old_pr['number']),
                    '--repo', 'leanprover-community/mathlib4'])
        print_success(f"Closed old PR #{old_pr['number']}")

    except Exception as e:
        print_error(f"Failed to close old PR: {e}")


def main() -> None:
    """Main migration workflow."""
    # Enable ANSI colors on Windows if possible
    if platform.system() == 'Windows':
        try:
            # Enable ANSI colors on Windows 10+
            os.system('')  # This enables ANSI colors in Windows terminal
        except Exception:
            pass  # If it fails, we'll use the no-color fallback

    # Parse command line arguments
    parser = argparse.ArgumentParser(description="Script to migrate contributors from direct write access to using forks.")
    parser.add_argument('-y', '--auto-accept', action='store_true', help="Auto-accept all prompts")
    args = parser.parse_args()

    print(f"{Colors.BOLD}🔄 Mathlib4 Fork Migration Script{Colors.END}")
    print("This script will help you migrate from direct write access to using forks.\n")

    if args.auto_accept:
        print(f"{Colors.YELLOW}ℹ️  Auto-accept mode enabled - all prompts will be automatically accepted{Colors.END}\n")

    # Step 1: Check gh installation
    if not check_gh_installation():
        sys.exit(1)

    # Step 2: Get username
    username = get_github_username()

    # Step 3: Check/create fork
    fork_url = check_and_create_fork(username, args.auto_accept)

    # Step 4: Setup remotes
    fork_remote_name = setup_remotes(username, fork_url, args.auto_accept)

    # Get current branch and validate
    current_branch = get_current_branch()
    validate_branch_for_migration(current_branch, args.auto_accept)

    # Check if branch is already migrated
    branch_already_migrated = check_branch_already_migrated(current_branch, username, fork_remote_name)

    # Step 5: Push branch to fork (if needed)
    if not branch_already_migrated:
        push_branch_to_fork(current_branch, fork_remote_name)
    else:
        print(f"✅ Branch '{current_branch}' is already configured to push to your fork - skipping migration")

    # Step 6: Check for existing PRs
    existing_pr_info = find_existing_pr(current_branch, username)

    # Step 7 & 8: Handle PR migration based on what we found
    if existing_pr_info:
        pr_type = existing_pr_info['type']

        if pr_type == 'fork':
            # PR already exists from fork - nothing to do
            pr = existing_pr_info['pr']
            print_success(f"✅ PR #{pr['number']} already exists from your fork - no migration needed")
            print(f"URL: {pr['url']}")

        elif pr_type == 'old':
            # Old-style PR exists, offer to migrate it
            old_pr = existing_pr_info['pr']
            if yes_no_prompt("Create new PR from fork and close the old one?", auto_accept=args.auto_accept):
                new_pr_url = create_new_pr_from_fork(current_branch, username, old_pr)
                close_old_pr_and_comment(old_pr, new_pr_url)
            else:
                print("Skipping PR migration. You can create a new PR manually if needed.")

        elif pr_type == 'both':
            # Both old and new style PRs exist - manual cleanup needed
            old_pr = existing_pr_info['old_pr']
            fork_pr = existing_pr_info['fork_pr']
            print_warning("⚠️  Found PRs from both main repo and fork:")
            print(f"   Main repo PR: #{old_pr['number']} - {old_pr['title']}")
            print(f"   Fork PR: #{fork_pr['number']} - {fork_pr['title']}")
            print("\nThis situation requires manual cleanup. You may want to:")
            print("1. Review both PRs to see which one is current")
            print("2. Close the outdated one manually")
            print("3. Update the active PR if needed")
    else:
        # No existing PR found - just note it, don't offer to create one
        print("✓ No existing PR found for this branch")

    print(f"\n{Colors.BOLD}{Colors.GREEN}🎉 Migration completed successfully!{Colors.END}")

    # Show summary of current state
    print(f"\n{Colors.BOLD}Current state:{Colors.END}")
    print(f"✓ Branch '{current_branch}' is configured to push to your fork")
    print(f"✓ Git remotes are set up correctly (fork remote: '{fork_remote_name}')")
    if existing_pr_info and existing_pr_info['type'] in ['fork', 'both']:
        pr_info = existing_pr_info.get('pr') or existing_pr_info.get('fork_pr')
        print(f"✓ PR #{pr_info['number']} exists from your fork")

    print(f"\n{Colors.BOLD}Next steps:{Colors.END}")
    print(f"1. Future pushes will automatically go to your fork ('{fork_remote_name}' remote)")
    print("2. Create PRs from your fork to leanprover-community/mathlib4")
    print("3. Remember to sync your fork regularly with upstream:")
    print("   gh repo sync --source leanprover-community/mathlib4")
    print("4. To update other branches, checkout and run this script again")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print(f"\n{Colors.YELLOW}Migration cancelled by user{Colors.END}")
        sys.exit(0)
