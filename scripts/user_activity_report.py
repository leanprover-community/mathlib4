#!/usr/bin/env python3
"""
Generate a report of repository users and their last commit activity.

This script finds all users with access to the repository, determines when they
last made a commit, and generates a table showing username, age of last commit,
and access level, sorted by age of last commit (most recent first).

Features:
- Fetches repository collaborators and organization members
- Caches user lists (24h expiry) and commit data (6h expiry) for performance
- Supports filtering by access level (--admin, --write)
- Supports single user analysis (--user USERNAME)
- Supports limiting results for debugging (--limit N)
- Can generate removal commands for inactive users (--remove N)
- Uses gh CLI for authenticated GitHub API access

The --remove flag generates (but does not execute) gh commands to remove
write access from non-admin users who haven't committed in more than N days.
Bot accounts (usernames ending with '-bot') are automatically excluded from
removal commands.

Results are cached to avoid repeated API calls. Cache files are automatically
saved after each new commit lookup to prevent data loss.

Requires 'gh' (GitHub CLI) to be installed and authenticated.
"""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# Get cache directory following XDG Base Directory Specification
cache_home = os.environ.get('XDG_CACHE_HOME')
if cache_home:
    CACHE_DIR = Path(cache_home) / "user_activity_report"
else:
    CACHE_DIR = Path.home() / ".cache" / "user_activity_report"


def get_cache_files(owner: str, repo: str) -> Tuple[Path, Path]:
    """Get repository-specific cache file paths."""
    # Ensure cache directory exists
    CACHE_DIR.mkdir(parents=True, exist_ok=True)

    # Replace slash with underscore to make it filesystem-safe
    repo_slug = f"{owner}_{repo}"
    users_cache_file = CACHE_DIR / f"users_cache_{repo_slug}.json"
    commits_cache_file = CACHE_DIR / f"commits_cache_{repo_slug}.json"
    return users_cache_file, commits_cache_file


def check_gh_auth() -> bool:
    """Check if gh is installed and authenticated."""
    try:
        result = subprocess.run(['gh', 'auth', 'status'], capture_output=True, text=True, check=False)
        return result.returncode == 0
    except FileNotFoundError:
        print("Error: 'gh' command not found. Please install GitHub CLI.", file=sys.stderr)
        return False


def get_repo_info(repo_arg: Optional[str] = None) -> Tuple[str, str]:
    """Get repository owner and name from command line argument or git remote."""
    if repo_arg:
        try:
            if '/' not in repo_arg:
                raise ValueError("Repository must be in format 'owner/repo'")
            owner, repo = repo_arg.split('/', 1)
            if not owner or not repo:
                raise ValueError("Repository must be in format 'owner/repo'")
            return owner, repo
        except ValueError as e:
            print(f"Error: Invalid repository format '{repo_arg}'. {e}", file=sys.stderr)
            sys.exit(1)

    # Fall back to git remote detection
    try:
        result = subprocess.run(
            ['git', 'remote', 'get-url', 'origin'],
            capture_output=True, text=True, check=True
        )
        url = result.stdout.strip()

        if url.startswith('git@github.com:'):
            # SSH format: git@github.com:owner/repo.git
            repo_path = url.replace('git@github.com:', '').replace('.git', '')
        elif url.startswith('https://github.com/'):
            # HTTPS format: https://github.com/owner/repo.git
            repo_path = url.replace('https://github.com/', '').replace('.git', '')
        else:
            raise ValueError(f"Unknown git remote format: {url}")

        owner, repo = repo_path.split('/')

        # If this is a fork of mathlib, use the upstream repository instead
        if repo.lower() == 'mathlib4' and owner != 'leanprover-community':
            print(f"Detected fork of mathlib ({owner}/{repo}), using upstream leanprover-community/mathlib4 instead")
            return 'leanprover-community', 'mathlib4'

        return owner, repo
    except (subprocess.CalledProcessError, ValueError, IndexError) as e:
        print(f"Error getting repository info: {e}", file=sys.stderr)
        print("Tip: Use --repo owner/repo to specify a repository manually", file=sys.stderr)
        sys.exit(1)


def get_repo_collaborators(owner: str, repo: str, limit: Optional[int] = None) -> List[Dict]:
    """Get repository collaborators using gh CLI."""
    print("Fetching repository collaborators...")

    collaborators = []

    # Get collaborators
    try:
        cmd = ['gh', 'api', f'repos/{owner}/{repo}/collaborators', '--paginate']
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        # The --paginate flag returns all pages concatenated as a single JSON array
        collaborators_data = json.loads(result.stdout)

        for collaborator in collaborators_data:
            collaborators.append(collaborator)
            if limit and len(collaborators) >= limit:
                break

    except subprocess.CalledProcessError as e:
        print(f"Warning: Could not fetch collaborators: {e}")
    except json.JSONDecodeError as e:
        print(f"Warning: Could not parse collaborators response: {e}")

    # Also try to get organization members if this is an org repo
    try:
        cmd = ['gh', 'api', f'orgs/{owner}/members', '--paginate']
        result = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if result.returncode == 0:
            org_members = json.loads(result.stdout)
            # Add org members who aren't already in collaborators list
            existing_logins = {c['login'] for c in collaborators}
            for member in org_members:
                if member['login'] not in existing_logins:
                    # Add with 'member' permission level
                    member['permissions'] = {'admin': False, 'maintain': False, 'push': False, 'triage': False, 'pull': True}
                    member['role_name'] = 'member'
                    collaborators.append(member)
                    if limit and len(collaborators) >= limit:
                        break
    except (subprocess.CalledProcessError, json.JSONDecodeError):
        # Org API might not be accessible, that's okay
        pass

    return collaborators


def get_contributors_fallback(owner: str, repo: str, limit: Optional[int] = None) -> List[Dict]:
    """Get repository contributors as fallback using gh CLI."""
    print("Fetching repository contributors (fallback)...")

    contributors = []

    try:
        cmd = ['gh', 'api', f'repos/{owner}/{repo}/contributors', '--paginate']
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        # The --paginate flag returns all pages concatenated as a single JSON array
        contributors_data = json.loads(result.stdout)

        for contributor in contributors_data:
            # Add with 'contributor' permission level
            contributor['permissions'] = {'admin': False, 'maintain': False, 'push': False, 'triage': False, 'pull': True}
            contributor['role_name'] = 'contributor'
            contributors.append(contributor)
            if limit and len(contributors) >= limit:
                break

    except subprocess.CalledProcessError as e:
        print(f"Warning: Could not fetch contributors: {e}")
    except json.JSONDecodeError as e:
        print(f"Warning: Could not parse contributors response: {e}")

    return contributors


def load_users_cache(owner: str, repo: str) -> Optional[List[Dict]]:
    """Load cached users data."""
    users_cache_file, commits_cache_file = get_cache_files(owner, repo)
    if users_cache_file.exists():
        try:
            with open(users_cache_file, 'r') as f:
                data = json.load(f)
                # Check if cache is less than 24 hours old
                cache_time = datetime.fromisoformat(data['timestamp'])
                if (datetime.now(timezone.utc) - cache_time).total_seconds() < 24 * 3600:
                    print("Using cached user data...")
                    return data['users']
        except (json.JSONDecodeError, KeyError, ValueError):
            pass
    return None


def save_users_cache(owner: str, repo: str, users: List[Dict]) -> None:
    """Save users data to cache."""
    users_cache_file, commits_cache_file = get_cache_files(owner, repo)
    cache_data = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'users': users
    }
    with open(users_cache_file, 'w') as f:
        json.dump(cache_data, f, indent=2)


def load_commits_cache(owner: str, repo: str) -> Dict[str, str]:
    """Load cached commit data."""
    users_cache_file, commits_cache_file = get_cache_files(owner, repo)
    if commits_cache_file.exists():
        try:
            with open(commits_cache_file, 'r') as f:
                data = json.load(f)
                # Check if cache is less than 6 hours old
                cache_time = datetime.fromisoformat(data['timestamp'])
                if (datetime.now(timezone.utc) - cache_time).total_seconds() < 6 * 3600:
                    print("Using cached commit data...")
                    return data['commits']
        except (json.JSONDecodeError, KeyError, ValueError):
            pass
    return {}


def save_commits_cache(owner: str, repo: str, commits: Dict[str, str]) -> None:
    """Save commit data to cache."""
    users_cache_file, commits_cache_file = get_cache_files(owner, repo)
    cache_data = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'commits': commits
    }
    with open(commits_cache_file, 'w') as f:
        json.dump(cache_data, f, indent=2)


def get_last_commit_for_user(owner: str, repo: str, username: str) -> Optional[str]:
    """Get the date of the last commit by a user using gh CLI."""
    try:
        # Use query string format for parameters
        cmd = ['gh', 'api', f'repos/{owner}/{repo}/commits?author={username}&per_page=1']
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        commits = json.loads(result.stdout)
        if commits:
            commit_date = commits[0]['commit']['author']['date']
            return commit_date
    except subprocess.CalledProcessError as e:
        print(f"Warning: Could not fetch commits for {username}: {e}")
    except json.JSONDecodeError as e:
        print(f"Warning: Could not parse commits response for {username}: {e}")

    return None


def format_time_ago(date_str: str) -> str:
    """Format a datetime string as 'X days ago' or similar."""
    if not date_str:
        return "Never"

    try:
        commit_date = datetime.fromisoformat(date_str.replace('Z', '+00:00'))
        now = datetime.now(timezone.utc)
        diff = now - commit_date

        days = diff.days
        if days == 0:
            hours = diff.seconds // 3600
            if hours == 0:
                minutes = diff.seconds // 60
                return f"{minutes} minute{'s' if minutes != 1 else ''} ago"
            return f"{hours} hour{'s' if hours != 1 else ''} ago"
        elif days == 1:
            return "1 day ago"
        elif days < 30:
            return f"{days} days ago"
        elif days < 365:
            months = days // 30
            return f"{months} month{'s' if months != 1 else ''} ago"
        else:
            years = days // 365
            return f"{years} year{'s' if years != 1 else ''} ago"
    except ValueError:
        return "Invalid date"


def get_permission_level(user_data: Dict) -> str:
    """Extract permission level from user data."""
    if 'role_name' in user_data:
        return user_data['role_name']

    permissions = user_data.get('permissions', {})
    if permissions.get('admin'):
        return 'admin'
    elif permissions.get('maintain'):
        return 'maintain'
    elif permissions.get('push'):
        return 'write'
    elif permissions.get('triage'):
        return 'triage'
    elif permissions.get('pull'):
        return 'read'
    else:
        return 'unknown'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, help='Limit the number of users to process (for debugging)')
    parser.add_argument('--user', type=str, help='Only show results for a specific user (for debugging)')
    parser.add_argument('--no-cache', action='store_true', help='Skip cache and fetch fresh data')
    parser.add_argument('--contributors-only', action='store_true', help='Use contributors API instead of collaborators (works without special permissions)')
    parser.add_argument('--write', action='store_true', help='Only show users with write access or higher')
    parser.add_argument('--admin', action='store_true', help='Only show users with admin access')
    parser.add_argument('--remove', type=int, metavar='N', help='Print gh commands to remove write access from non-admin users inactive for more than N days (does not execute)')
    parser.add_argument('--repo', type=str, help='Specify a repository in the format "owner/repo" (defaults to current git repository)')

    args = parser.parse_args()

    # Check gh authentication
    if not check_gh_auth():
        print("Error: 'gh' is not authenticated. Please run 'gh auth login' first.", file=sys.stderr)
        sys.exit(1)

    # Get repository info
    owner, repo = get_repo_info(args.repo)
    print(f"Analyzing repository: {owner}/{repo}")

    # Get users with access
    users = None if args.no_cache else load_users_cache(owner, repo)
    if users is None:
        if args.contributors_only:
            users = get_contributors_fallback(owner, repo, args.limit)
        else:
            users = get_repo_collaborators(owner, repo, args.limit)
            # If no collaborators found (e.g., no access), fall back to contributors
            if not users:
                print("No collaborators found, falling back to contributors...")
                users = get_contributors_fallback(owner, repo, args.limit)
        save_users_cache(owner, repo, users)

    # Apply limit to cached data as well
    if args.limit and len(users) > args.limit:
        users = users[:args.limit]

    # Apply access level filters
    if args.admin or args.write:
        filtered_users = []
        for user in users:
            permission_level = get_permission_level(user)
            if args.admin and permission_level == 'admin':
                filtered_users.append(user)
            elif args.write and permission_level in ['write', 'admin', 'maintain']:
                filtered_users.append(user)
        users = filtered_users
        if not users:
            print("No users found matching the specified access level criteria.")
            sys.exit(1)

    if args.user:
        users = [user for user in users if user['login'] == args.user]
        if not users:
            print(f"User '{args.user}' not found in repository collaborators/contributors.")
            # Try to get commit info for this user anyway
            users = [{
                'login': args.user,
                'html_url': f'https://github.com/{args.user}',
                'permissions': {},
                'role_name': 'unknown'
            }]

    if not users:
        print("No users found to analyze.")
        sys.exit(1)

    print(f"Processing {len(users)} users...")

    # Get cached commit data
    cached_commits = {} if args.no_cache else load_commits_cache(owner, repo)

    # Get last commit for each user
    user_commits = []

    for i, user in enumerate(users, 1):
        username = user['login']

        # Check cache first - distinguish between "not cached" vs "cached as None"
        if username in cached_commits:
            last_commit_date = cached_commits[username]
            print(f"Using cached data for {username} ({i}/{len(users)})...")
        else:
            print(f"Fetching commits for {username} ({i}/{len(users)})...")
            last_commit_date = get_last_commit_for_user(owner, repo, username)
            cached_commits[username] = last_commit_date
            # Save cache after each new lookup
            save_commits_cache(owner, repo, cached_commits)

        permission_level = get_permission_level(user)

        user_commits.append({
            'username': username,
            'last_commit_date': last_commit_date,
            'permission_level': permission_level,
            'profile_url': user['html_url']
        })

    # Sort by last commit date (most recent first, then never committed)
    def sort_key(user_data):
        if user_data['last_commit_date'] is None:
            # Never committed users should be treated as the oldest (very early date)
            return datetime.min.replace(tzinfo=timezone.utc)
        try:
            # Parse the ISO date string
            commit_date = datetime.fromisoformat(user_data['last_commit_date'].replace('Z', '+00:00'))
            return commit_date
        except ValueError:
            # If date parsing fails, treat as very old
            return datetime.min.replace(tzinfo=timezone.utc)

    user_commits.sort(key=sort_key, reverse=True)

    # Handle --remove flag
    if args.remove is not None:
        print(f"\n{'='*80}")
        print(f"COMMANDS TO REMOVE INACTIVE NON-ADMIN USERS (>{args.remove} days)")
        print(f"{'='*80}")
        print("# The following commands would remove write access from non-admin users")
        print("# who haven't committed in more than {} days:".format(args.remove))
        print("# (Bot accounts ending with '-bot' are excluded)")
        print()

        now = datetime.now(timezone.utc)
        cutoff_date = now - timedelta(days=args.remove)
        removal_commands = []

        for user_data in user_commits:
            username = user_data['username']
            permission_level = user_data['permission_level']
            last_commit_date = user_data['last_commit_date']

            # Skip bot accounts
            if username.endswith('-bot'):
                continue

            # Only consider non-admin users with write access
            if permission_level in ['write', 'maintain'] and permission_level != 'admin':
                should_remove = False

                if last_commit_date is None:
                    # Never committed - should be removed
                    should_remove = True
                    reason = "never committed"
                else:
                    try:
                        commit_date = datetime.fromisoformat(last_commit_date.replace('Z', '+00:00'))
                        if commit_date < cutoff_date:
                            days_ago = (now - commit_date).days
                            should_remove = True
                            reason = f"last commit {days_ago} days ago"
                    except ValueError:
                        # If we can't parse the date, treat as old
                        should_remove = True
                        reason = "unparsable commit date"

                if should_remove:
                    cmd = f"gh api repos/{owner}/{repo}/collaborators/{username} -X DELETE"
                    removal_commands.append((cmd, username, reason))

        if removal_commands:
            for cmd, username, reason in removal_commands:
                print(cmd)
            print(f"\n# Total users to remove: {len(removal_commands)}")
        else:
            print("# No users found matching removal criteria")

        print(f"\n# NOTE: These commands are NOT executed automatically.")
        print(f"# Review carefully before running any of these commands.")
        return

    # Generate report
    print("\n" + "="*80)
    print("REPOSITORY USER ACTIVITY REPORT")
    print("="*80)
    print(f"Repository: {owner}/{repo}")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Total users analyzed: {len(user_commits)}")
    print()

    # Table header
    print(f"{'Username':<25} {'Last Commit':<20} {'Access Level':<15} {'Profile'}")
    print("-" * 80)

    for user_data in user_commits:
        username = user_data['username']
        last_commit = format_time_ago(user_data['last_commit_date'])
        permission = user_data['permission_level']
        profile_url = user_data['profile_url']

        print(f"{username:<25} {last_commit:<20} {permission:<15} {profile_url}")

    print()
    print(f"Note: Cached data is used when less than 24 hours old (users) or 6 hours old (commits).")
    print(f"Use --no-cache to force fresh data retrieval.")


if __name__ == '__main__':
    main()
