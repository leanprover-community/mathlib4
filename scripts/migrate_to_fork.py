#!/usr/bin/env python3
"""
Script to migrate contributors from direct write access to using forks.

This script automates the process of migrating mathlib4 contributors from having
direct write access to the main repository to using a fork-based workflow.

Features:
1. Validates current branch (prevents migration of system branches like master, nightly-testing)
2. Checks GitHub CLI installation and authentication with OS-specific installation instructions
3. Creates or syncs user's fork of mathlib4
4. Sets up git remotes correctly (upstream → leanprover-community/mathlib4, origin → user's fork)
5. Detects if migration has already been completed and skips unnecessary steps
6. Migrates current branch to fork with proper upstream tracking
7. Intelligently handles existing PRs:
   - Detects open PRs from main repo and offers to migrate them to fork-based PRs
   - Detects existing fork-based PRs and confirms no migration needed
   - Handles edge cases with both main repo and fork PRs requiring manual cleanup
8. Uses fast delete/re-add approach for remote changes to avoid slow branch tracking updates
9. Provides comprehensive status reporting and next steps

Usage:
  python3 scripts/migrate_to_fork.py           # Interactive mode
  python3 scripts/migrate_to_fork.py -y        # Auto-accept all prompts

Requirements:
  - GitHub CLI (gh) installed and authenticated (gh auth login)
  - Git repository must be the mathlib4 repository
  - User must be on a feature branch (not master, nightly-testing, or lean-pr-testing-*)

The script is safe to run multiple times and will skip already-completed migration steps.
"""

import subprocess
import sys
import json
import re
import argparse
from typing import Optional, Dict, Any, List


class Colors:
    """ANSI color codes for terminal output."""
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
    """Run a command and return the result."""
    try:
        result = subprocess.run(cmd, capture_output=capture_output, text=True, check=check)
        return result
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
        return True
    except Exception:
        print_error("Failed to check GitHub CLI authentication status.")
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


def check_and_create_fork(username: str, auto_accept: bool = False) -> str:
    """Check if user has a fork, create one if needed."""
    print_step(3, "Checking for fork of mathlib4")

    repo_name = f"{username}/mathlib4"

    # Check if fork exists
    try:
        result = run_command(['gh', 'repo', 'view', repo_name], check=False)
        if result.returncode == 0:
            print_success(f"Fork exists: {repo_name}")

            # Synchronize master branch
            print("Synchronizing fork's master branch...")
            try:
                run_command(['gh', 'repo', 'sync', repo_name, '--source', 'leanprover-community/mathlib4'])
                print_success("Fork synchronized with upstream")
            except Exception as e:
                print_warning(f"Failed to sync fork automatically: {e}")
                print("You may need to sync manually later")

            return f"git@github.com:{repo_name}.git"
    except Exception:
        pass

    # Fork doesn't exist, offer to create it
    print(f"Fork {repo_name} does not exist.")
    if yes_no_prompt("Would you like to create a fork?", auto_accept=auto_accept):
        try:
            print("Creating fork...")
            run_command(['gh', 'repo', 'fork', 'leanprover-community/mathlib4', '--clone=false'])
            print_success(f"Fork created: {repo_name}")
            return f"git@github.com:{repo_name}.git"
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


def setup_remotes(username: str, fork_url: str, auto_accept: bool = False) -> None:
    """Set up upstream and origin remotes correctly."""
    print_step(4, "Setting up git remotes")

    remotes = get_current_remotes()
    upstream_url = "git@github.com:leanprover-community/mathlib4.git"
    upstream_https = "https://github.com/leanprover-community/mathlib4.git"

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

    # Handle origin remote (fork)
    origin_remote = None
    for name, url in remotes.items():
        if f'{username}/mathlib4' in url:
            origin_remote = name
            break

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
        else:
            print_success("Origin remote (fork) already configured correctly")
    else:
        # Check if origin exists and is not the fork
        if 'origin' in remotes:
            if f'{username}/mathlib4' not in remotes['origin']:
                print(f"Current origin: {remotes['origin']}")
                if yes_no_prompt("Replace existing 'origin' with your fork?", auto_accept=auto_accept):
                    run_command(['git', 'remote', 'remove', 'origin'])
                    run_command(['git', 'remote', 'add', 'origin', fork_url])
                    print_success("Set origin to your fork")
                else:
                    run_command(['git', 'remote', 'add', 'fork', fork_url])
                    print_warning("Added fork as 'fork' remote instead of 'origin'")
            else:
                print_success("Origin already points to your fork")
        else:
            run_command(['git', 'remote', 'add', 'origin', fork_url])
            print_success("Added origin remote pointing to your fork")


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
    invalid_branches = []

    if branch == 'master':
        invalid_branches.append("master (main development branch)")
    elif branch == 'nightly-testing':
        invalid_branches.append("nightly-testing (CI testing branch)")
    elif re.match(r'^lean-pr-testing-\d+$', branch):
        invalid_branches.append(f"{branch} (Lean PR testing branch)")

    if invalid_branches:
        print_error(f"Cannot migrate branch '{branch}'")
        print(f"The branch '{branch}' is a system branch that should not be migrated to a fork.")
        print("\nSystem branches that cannot be migrated:")
        for invalid_branch in invalid_branches:
            print(f"  • {invalid_branch}")

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


def check_branch_already_migrated(branch: str, username: str) -> bool:
    """Check if the current branch is already set to push to the user's fork."""
    try:
        # Get the upstream branch for the current branch
        result = run_command(['git', 'rev-parse', '--abbrev-ref', f'{branch}@{{upstream}}'], check=False)
        if result.returncode == 0:
            upstream = result.stdout.strip()
            # Check if upstream is origin/branch (which should point to the fork)
            if upstream.startswith('origin/'):
                # Verify that origin actually points to the user's fork
                remotes = get_current_remotes()
                if 'origin' in remotes and f'{username}/mathlib4' in remotes['origin']:
                    print_success(f"Branch '{branch}' is already configured to push to your fork")
                    return True
        return False
    except Exception:
        return False


def push_branch_to_fork(branch: str) -> None:
    """Push current branch to fork and set upstream."""
    print_step(5, f"Pushing branch '{branch}' to fork")

    try:
        # Push to fork and set upstream
        run_command(['git', 'push', '-u', 'origin', branch])
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
        result = run_command(['gh', 'pr', 'list', '--repo', 'leanprover-community/mathlib4',
                             '--head', f'{branch}', '--json', 'number,title,url,state,headRepositoryOwner'],
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
                        print_success(f"Found existing open PR from main repo: #{pr['number']} - {pr['title']}")
                        print(f"URL: {pr['url']}")
                    elif head_repo_owner == username:
                        # PR from user's fork
                        fork_style_pr = pr
                        print_success(f"Found existing open PR from your fork: #{pr['number']} - {pr['title']}")
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


def create_new_pr_from_fork(branch: str, username: str, old_pr: Optional[Dict[str, Any]] = None) -> str:
    """Create a new PR from the fork."""
    print_step(7, "Creating new PR from fork")

    try:
        # Get PR details
        if old_pr:
            title = old_pr['title']
            print(f"Using title from old PR: {title}")
        else:
            title = get_user_input("Enter PR title")

        # Create PR from fork
        cmd = ['gh', 'pr', 'create',
               '--repo', 'leanprover-community/mathlib4',
               '--head', f'{username}:{branch}',
               '--title', title]

        if old_pr:
            body = f"This PR continues the work from #{old_pr['number']}.\n\nOriginal PR: {old_pr['url']}"
            cmd.extend(['--body', body])  # Add body as separate arguments
        else:
            cmd.extend(['--body', ''])  # Empty body for new PRs

        result = run_command(cmd)

        # Extract PR URL from output
        pr_url = result.stdout.strip()
        print_success(f"New PR created: {pr_url}")

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

        # Close old PR
        run_command(['gh', 'pr', 'close', str(old_pr['number']),
                    '--repo', 'leanprover-community/mathlib4'])
        print_success(f"Closed old PR #{old_pr['number']}")

    except Exception as e:
        print_error(f"Failed to close old PR: {e}")


def main() -> None:
    """Main migration workflow."""
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
    setup_remotes(username, fork_url, args.auto_accept)

    # Get current branch and validate
    current_branch = get_current_branch()
    validate_branch_for_migration(current_branch, args.auto_accept)

    # Check if branch is already migrated
    branch_already_migrated = check_branch_already_migrated(current_branch, username)

    # Step 5: Push branch to fork (if needed)
    if not branch_already_migrated:
        push_branch_to_fork(current_branch)
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
    print("✓ Git remotes are set up correctly")
    if existing_pr_info and existing_pr_info['type'] in ['fork', 'both']:
        pr_info = existing_pr_info.get('pr') or existing_pr_info.get('fork_pr')
        print(f"✓ PR #{pr_info['number']} exists from your fork")

    print(f"\n{Colors.BOLD}Next steps:{Colors.END}")
    print("1. Future pushes will automatically go to your fork")
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
