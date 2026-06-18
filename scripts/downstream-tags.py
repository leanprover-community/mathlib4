#!/usr/bin/env python3

import yaml
import sys
import subprocess
import re
from typing import List, Dict, Optional
import json
import base64
import shutil

# Unicode symbols
TICK = "✅"   # Check mark button
CROSS = "❌"  # Cross mark

def check_gh_installed():
    """Check if GitHub CLI (gh) is installed and accessible"""
    if not shutil.which('gh'):
        print("Error: GitHub CLI (gh) is not installed or not in PATH", file=sys.stderr)
        print("Please install it from https://cli.github.com/", file=sys.stderr)
        sys.exit(1)

def load_repos() -> List[Dict[str, str]]:
    """Load repository information from downstream_repos.yml"""
    with open('scripts/downstream_repos.yml', 'r') as f:
        return yaml.safe_load(f)

def get_file_path(repo: Dict[str, str], relative_path: str) -> str:
    """Construct the full path to a file in the repository, accounting for the optional 'path' field"""
    repo_path = repo.get('path', '')
    if repo_path:
        return f"{repo_path}/{relative_path}"
    return relative_path

def check_tag(repo: Dict[str, str], tag: str) -> bool:
    """Check if a tag exists in a repository using GitHub CLI"""
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/git/refs/tags/{tag}'],
            capture_output=True,
            text=True
        )
        return result.returncode == 0
    except subprocess.CalledProcessError:
        return False

def get_latest_version(repo: Dict[str, str]) -> Optional[str]:
    """Get the latest version tag from a repository"""
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/git/refs/tags'],
            capture_output=True,
            text=True
        )
        if result.returncode != 0:
            return None

        # Parse JSON response
        tags = json.loads(result.stdout)

        # Extract tag names and filter for version tags
        version_pattern = re.compile(r'v4\.\d+\.\d+(?:-rc\d+)?$')
        version_tags = []

        for tag in tags:
            ref = tag['ref']
            tag_name = ref.replace('refs/tags/', '')
            if version_pattern.match(tag_name):
                version_tags.append(tag_name)

        if not version_tags:
            return None

        # Sort version tags
        def version_key(tag):
            # Split into parts: v4.17.0-rc1 -> [4, 17, 0, 1]
            parts = tag[1:].split('.')  # Remove 'v' prefix
            major, minor = parts[0:2]
            patch_rc = parts[2].split('-')
            patch = int(patch_rc[0])
            # RC versions should sort before final versions
            rc = int(patch_rc[1][2:]) if len(patch_rc) > 1 else float('inf')
            return (int(major), int(minor), patch, rc)

        return max(version_tags, key=version_key)
    except Exception as e:
        print(f"Error fetching tags for {repo['name']}: {e}", file=sys.stderr)
        return None

def check_toolchain_history(repo: Dict[str, str], version: str) -> Optional[str]:
    """Check git history of lean-toolchain file for first occurrence of version"""
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')
    toolchain_path = get_file_path(repo, 'lean-toolchain')

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/commits?path={toolchain_path}'],
            capture_output=True,
            text=True
        )
        if result.returncode != 0:
            return None

        commits = json.loads(result.stdout)

        for commit in commits:
            sha = commit['sha']
            result = subprocess.run(
                ['gh', 'api', f'repos/{repo_name}/contents/{toolchain_path}?ref={sha}'],
                capture_output=True,
                text=True
            )
            if result.returncode == 0:
                content = json.loads(result.stdout)
                toolchain = base64.b64decode(content['content']).decode('utf-8').strip()
                # Check for exact match
                if toolchain == f'leanprover/lean4:{version}':
                    return commit['sha']
        return None
    except Exception as e:
        print(f"Error checking toolchain history for {repo['name']}: {e}", file=sys.stderr)
        return None

def get_current_toolchain(repo: Dict[str, str]) -> Optional[str]:
    """Get the current toolchain version from the default branch"""
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')
    toolchain_path = get_file_path(repo, 'lean-toolchain')

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/contents/{toolchain_path}'],
            capture_output=True,
            text=True
        )
        if result.returncode == 0:
            content = json.loads(result.stdout)
            toolchain = base64.b64decode(content['content']).decode('utf-8').strip()
            # Strip the prefix if present
            return toolchain.replace('leanprover/lean4:', '')
        return None
    except Exception:
        return None

def main():
    # Add gh check at the start of main
    check_gh_installed()

    repos = load_repos()

    if len(sys.argv) == 1:
        # Collect data with progress spinner
        repo_data = []
        total = len(repos)
        for i, repo in enumerate(repos, 1):
            print(f"\rCollecting data: {i}/{total}", end='', flush=True)
            latest = get_latest_version(repo)
            current = get_current_toolchain(repo)
            repo_data.append({
                'repo': repo,
                'latest': latest,
                'current': current
            })
        print()  # New line after spinner

        # Group repos by toolchain version
        from collections import defaultdict
        by_version = defaultdict(list)
        no_tags = []

        for data in repo_data:
            if data['latest']:
                by_version[data['latest']].append(data)
            else:
                no_tags.append(data)

        # Sort versions from newest to oldest
        def version_key(tag):
            parts = tag[1:].split('.')  # Remove 'v' prefix
            major, minor = parts[0:2]
            patch_rc = parts[2].split('-')
            patch = int(patch_rc[0])
            # RC versions should sort before final versions
            rc = int(patch_rc[1][2:]) if len(patch_rc) > 1 else float('inf')
            return (int(major), int(minor), patch, rc)

        sorted_versions = sorted(by_version.keys(), key=version_key, reverse=True)

        # Display results
        print("\nDownstream repositories by toolchain version:")
        print("=" * 50)

        for version in sorted_versions:
            print(f"\n{version}:")
            for data in by_version[version]:
                print(f"  {TICK} {data['repo']['name']}")

        if no_tags:
            print(f"\nNo toolchain tags:")
            for data in no_tags:
                current_str = f" (on {data['current']})" if data['current'] else ""
                print(f"  {CROSS} {data['repo']['name']}{current_str}")

        sys.exit(0 if sorted_versions else 1)

    elif len(sys.argv) == 2:
        tag = sys.argv[1]
        print(f"Checking for tag {tag} in downstream repositories:")
        print("-" * 50)

        all_exist = True
        for repo in repos:
            exists = check_tag(repo, tag)
            status = TICK if exists else CROSS
            print(f"{status} {repo['name']}")
            if not exists:
                all_exist = False
                if commit := check_toolchain_history(repo, tag):
                    print("    - There is a commit which uses this toolchain. You can tag it using:")
                    print(f"    gh api repos/{repo['github'].replace('https://github.com/', '')}/git/refs "
                          f"-X POST -F ref=refs/tags/{tag} -F sha={commit}")
                else:
                    print("    - No matching toolchain found in history")

        sys.exit(0 if all_exist else 1)

    else:
        print("Usage: ./downstream-tags.py [tag]")
        sys.exit(1)

if __name__ == "__main__":
    main()
