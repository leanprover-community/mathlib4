#!/usr/bin/env python3

"""This script lists projects downstream from Mathlib and checks their setup:

* Do they have a release tag for the latest Lean version?
* How is their CI set up?
* What linting and testing do they do?

Based on the results, it makes actionable suggestions.
"""

import yaml
import sys
import subprocess
import re
from typing import Dict, Iterator, List, Optional
import json
import base64
import shutil

# Unicode symbols
# We don't want to enforce that every project is set up the same,
# just make a suggestion for tools that could be used.
# So WARN/FAIL is really: "we have an easier way to do this" and "have you considered trying this?"
PASS = "✅" # Success: check mark button
WARN = "💡" # Warning: lightbulb
FAIL = "🛠️" # Failure: work in progress

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

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/commits?path=lean-toolchain'],
            capture_output=True,
            text=True
        )
        if result.returncode != 0:
            return None

        commits = json.loads(result.stdout)

        for commit in commits:
            sha = commit['sha']
            result = subprocess.run(
                ['gh', 'api', f'repos/{repo_name}/contents/lean-toolchain?ref={sha}'],
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

def fetch_file_contents(repo: Dict[str, str], path: str) -> Optional[str]:
    """Get the contents at the path on the current branch.

    Returns None if the file could not be found.
    """
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')

    try:
        result = subprocess.run(
            ['gh', 'api', f'repos/{repo_name}/contents/{path}'],
            capture_output=True,
            text=True
        )
        if result.returncode == 0:
            content = json.loads(result.stdout)
            return base64.b64decode(content['content']).decode('utf-8')
        return None
    except Exception:
        return None

def get_current_toolchain(repo: Dict[str, str]) -> Optional[str]:
    """Get the current toolchain version from the default branch"""
    github_url = repo['github']
    repo_name = github_url.replace('https://github.com/', '')

    try:
        toolchain = fetch_file_contents(repo, 'lean-toolchain').strip()
        # Strip the prefix if present
        return toolchain.replace('leanprover/lean4:', '')
    except Exception:
        return None

def workflow_actions(workflow: Dict) -> Iterator[str]:
    """Iterator for all the actions invoked by the workflow.

    Each yielded string should be the full reference to the action, of the format 'owner/repo@ref'.
    """
    for job in workflow['jobs'].values():
        for step in job['steps']:
            try:
                yield step['uses']
            except KeyError:
                continue

def check_workflow_uses_action(repo: Dict[str, str], workflow_name: str, expected_action: str, silent=False) -> bool:
    """Check that the repository has a workflow for running the indicated CI job,
    and that this workflow invokes the indicated action.

    Will print its findings to stdout, unless `silent=True` is passed.
    """

    try:
        workflow_filename = repo['workflows'][workflow_name]
    except KeyError:
        if not silent:
            # Splat out the repo data and workflow data in order to not mutate the original.
            existing_workflows = repo.get('workflows', {})
            example_entry = {**repo, 'workflows': {**existing_workflows, workflow_name: f'{workflow_name}.yml'}}
            yaml_example_entry = yaml.dump(example_entry)
            print(
f"""  {FAIL} Consider adding a {workflow_name} workflow.
    See https://github.com/{expected_action}/blob/HEAD/README.md for installation instructions.
    After installing a workflow, please add an entry to `scripts/downstream_repos.yml` in Mathlib.
    For example, assuming you call the workflow file `{workflow_name}.yml`:
```
{yaml_example_entry}
```""")
        return False
    workflow_path = f'.github/workflows/{workflow_filename}'
    workflow_contents = fetch_file_contents(repo, workflow_path)
    if workflow_contents is None:
        if not silent:
            print(
f"""  {FAIL} Workflow {workflow_name}, file `{workflow_filename}` could not be fetched.
    Please ensure Mathlib's `scripts/downstream_repos.yml` refers to the correct file name (of the form `{workflow_name}.yml`).""")
        return False
    try:
        workflow = yaml.safe_load(workflow_contents)
    except Exception:
        if not silent:
            print(
f"""  {FAIL} Workflow {workflow_name} defined in `scripts/downstream_repos.yml` could not be parsed.
    Please ensure Mathlib's `scripts/downstream_repos.yml` refers to the correct file name (of the form `{workflow_name}.yml`).""")
        return False

    action_references = set(action.split('@')[0] for action in workflow_actions(workflow))
    if expected_action in action_references:
        if not silent:
            print(f"  {PASS} Detected workflow {workflow_name}, using the action: {expected_action}")
        return True
    else:
        if not silent:
            print(
f"""  {WARN} Detected a workflow {workflow_name} set up by hand.
    A GitHub Action exists to handle this workflow for you.
    See https://github.com/{expected_action}/blob/HEAD/README.md for installation instructions.""")
        return False

def main():
    # Add gh check at the start of main
    check_gh_installed()

    repos = load_repos()

    print("Checking downstream repository setup")
    print("-" * 50)

    success = True
    for repo in repos:
        print(f"\nRepository {repo['name']}")

        # Check toolchain versions.
        latest = get_latest_version(repo)
        if latest:
            print(f"  {PASS} Latest toolchain tag: {latest}")
        else:
            success = False
            current = get_current_toolchain(repo)
            print(
f"""  {FAIL} No toolchain tags found.
    Adding a tag for new releases helps users of your project to synchronize versions.
    A GitHub Action exists to handle tagging new releases for you.
    See https://github.com/leanprover-community/lean-release-tag/blob/HEAD/README.md for installation instructions.""")

        success = check_workflow_uses_action(repo, 'build', 'leanprover/lean-action') and success
        success = check_workflow_uses_action(repo, 'docs', 'leanprover-community/docgen-action') and success
        success = check_workflow_uses_action(repo, 'release-tag', 'leanprover-community/lean-release-tag') and success
        # We have two actions that can do auto-updating; handle these checks manually.
        if check_workflow_uses_action(repo, 'update', 'leanprover-community/lean-update', silent=True):
            print(f"  {PASS} Update workflow installed, using the action: leanprover-community/lean-update")
        else:
            # Report failure for mathlib-update-action, since that has more features.
            success = check_workflow_uses_action(repo, 'update', 'leanprover-community/mathlib-update-action') and success

        license = fetch_file_contents(repo, 'LICENSE')
        if license is not None:
            first_line = license.split('\n')[0].strip()
            print(f"  {PASS} License: {first_line}")
        else:
            success = False
            print(
f"""  {FAIL} Consider adding a license.
    Choosing a license for your project makes it open-source and encourages contribution and reuse.
    Lean and Mathlib are open-source projects available under the Apache License 2.0: https://choosealicense.com/licenses/apache-2.0/
    For instructions on how to apply a license, please see: https://docs.github.com/en/communities/setting-up-your-project-for-healthy-contributions/adding-a-license-to-a-repository""")

        # Determine lakefile contents: this can be found either in `lakefile.lean` or `lakefile.toml`.
        # (Check in this order to match Lake's own behaviour.)
        lakefile_format = 'lean'
        lakefile = fetch_file_contents(repo, 'lakefile.lean')
        if lakefile is None:
            lakefile_format = 'toml'
            lakefile = fetch_file_contents(repo, 'lakefile.toml')
            if lakefile is None:
                success = False
                print(
f"""  {FAIL} No lakefile found.
    This may be caused by a temporary network error. Try running the script again.""")
                continue
        # We're not going to parse the whole lakefile to check for these options.
        if 'lintDriver' in lakefile or 'lint_driver' in lakefile:
            print(f"  {PASS} Linting enabled.")
        else:
            success = False
            print(
f"""  {FAIL} Consider adding a lint driver.
    You can configure the `lake lint` command to automatically report code quality suggestions.
    Linters are included with Mathlib or Batteries.
    For instructions on enabling a linter, please see: https://github.com/leanprover-community/mathlib4/wiki/Setting-up-linting-and-testing-for-your-Lean-project#adding-a-linter""")
        if 'linter.mathlibStandard' in lakefile:
            # These linter options are quite strict, so don't complain if they are not enabled.
            print(f"  {PASS} Linting to Mathlib's standards.")
        if 'testDriver' in lakefile or 'test_driver' in lakefile:
            print(f"  {PASS} Testing enabled.")
        else:
            success = False
            # A warning, since a lot of projects seem to be their own test-suite.
            print(
f"""  {WARN} Consider adding a test driver.
    You can configure the `lake test` command to build and run test files.
    For instructions on creating a test suite, please see: https://github.com/leanprover-community/mathlib4/wiki/Setting-up-linting-and-testing-for-your-Lean-project#adding-a-test-driver""")

    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
