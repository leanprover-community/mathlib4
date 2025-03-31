#!/usr/bin/env python3

import json
import subprocess
import sys

def get_json_at_rev(rev, filename):
    """Get contents of JSON file at specific revision"""
    try:
        result = subprocess.run(
            ['git', 'show', f'{rev}:{filename}'],
            capture_output=True,
            text=True,
            check=True
        )
        return json.loads(result.stdout)
    except subprocess.CalledProcessError:
        print(f"Error: Failed to get {filename} at revision {rev}", file=sys.stderr)
        return None

def find_package_changes(old_manifest, new_manifest):
    """Compare two manifest files and find package version changes"""
    changes = []

    # Create lookup tables by package name
    old_packages = {pkg['name']: pkg for pkg in old_manifest['packages']}
    new_packages = {pkg['name']: pkg for pkg in new_manifest['packages']}

    # Find packages with different revisions and new packages
    for name, new_pkg in new_packages.items():
        if name in old_packages:
            old_pkg = old_packages[name]
            if old_pkg['rev'] != new_pkg['rev']:
                changes.append({
                    'type': 'update',
                    'dependency': name,
                    'old_version': old_pkg['rev'],
                    'new_version': new_pkg['rev'],
                    'url': new_pkg['url']
                })
        else:
            changes.append({
                'type': 'add',
                'dependency': name,
                'version': new_pkg['rev'],
                'url': new_pkg['url']
            })

    # Find removed packages
    for name in old_packages:
        if name not in new_packages:
            changes.append({
                'type': 'remove',
                'dependency': name,
                'version': old_packages[name]['rev'],
                'url': old_packages[name]['url']
            })

    return changes

def get_github_diff_url(pkg_url, old_rev, new_rev):
    """Convert a package URL to a GitHub compare URL"""
    # For updates: compare URL
    if old_rev and new_rev:
        return f"{pkg_url}/compare/{old_rev}...{new_rev}"
    # For additions: single new commit URL
    elif new_rev is not None and old_rev is None:
        return f"{pkg_url}/commit/{new_rev}"
    # For removals: single old commit URL
    elif old_rev is not None and new_rev is None:
        return f"{pkg_url}/commit/{old_rev}"
    # Handle case where no revisions are provided
    else:
        return pkg_url

def format_changes(changes):
    """Format the changes into a readable message"""
    if not changes:
        return "No dependency versions were changed"

    def short_hash(hash):
        """Return first 7 characters of commit hash"""
        return hash[:7]

    lines = []
    updates = [c for c in changes if c['type'] == 'update']
    additions = [c for c in changes if c['type'] == 'add']
    removals = [c for c in changes if c['type'] == 'remove']

    if updates:
        lines.append("The following dependencies were updated:")
        for change in updates:
            url = get_github_diff_url(change['url'], change['old_version'], change['new_version'])
            lines.append(f"* {change['dependency']}: {short_hash(change['old_version'])} → {short_hash(change['new_version'])} [[GitHub link]]({url})")

    if additions:
        if lines: lines.append("")
        lines.append("The following dependencies were added:")
        for change in additions:
            url = get_github_diff_url(change['url'], None, change['version'])
            lines.append(f"* {change['dependency']}: {short_hash(change['version'])} [[GitHub link]]({url})")

    if removals:
        if lines: lines.append("")
        lines.append("The following dependencies were removed:")
        for change in removals:
            url = get_github_diff_url(change['url'], change['version'], None)
            lines.append(f"* {change['dependency']}: {short_hash(change['version'])} [[GitHub link]]({url})")

    return "\n".join(lines)

def main():
    old_manifest = get_json_at_rev('HEAD~1', 'lake-manifest.json')
    if not old_manifest:
        raise SystemExit("Failed to read old lake-manifest.json at HEAD~1")

    new_manifest = get_json_at_rev('HEAD', 'lake-manifest.json')
    if not new_manifest:
        raise SystemExit("Failed to read new lake-manifest.json at HEAD")

    changes = find_package_changes(old_manifest, new_manifest)
    message = format_changes(changes)
    print(message)

if __name__ == "__main__":
    main()
