#!/usr/bin/env python3

import json
import subprocess
import sys

def get_git_diff():
    """Get the git diff for lake-manifest.json between HEAD and HEAD~1"""
    try:
        result = subprocess.run(
            ['git', 'diff', 'HEAD~1..HEAD', '--', 'lake-manifest.json'],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError:
        print("Error: Failed to get git diff", file=sys.stderr)
        return None

def parse_manifest_changes(diff_text):
    """Parse the diff to find version changes in dependencies"""
    changes = []
    old_version = None
    new_version = None
    package_name = None

    lines = diff_text.split('\n')
    for i, line in enumerate(lines):
        # When we find a rev change
        if line.startswith('-   "rev":'):
            old_version = line.split('"')[3]
            # Look ahead for the new version
            for next_line in lines[i:]:
                if next_line.startswith('+   "rev":'):
                    new_version = next_line.split('"')[3]
                    # Look ahead for the package name
                    for name_line in lines[i:]:
                        if name_line.startswith('   "name":'):
                            package_name = name_line.split('"')[3]
                            changes.append({
                                'dependency': package_name,
                                'old_version': old_version,
                                'new_version': new_version
                            })
                            break
                    break
            # Reset for next package
            old_version = None
            new_version = None
            package_name = None

    return changes

def format_changes(changes):
    """Format the changes into a readable message"""
    if not changes:
        return "No dependency versions were changed"

    lines = ["The following dependencies were updated:"]
    for change in changes:
        lines.append(f"* {change['dependency']}: {change['old_version']} → {change['new_version']}")

    return "\n".join(lines)

def main():
    diff = get_git_diff()
    if not diff:
        print("No changes found in lake-manifest.json")
        return 1

    changes = parse_manifest_changes(diff)
    message = format_changes(changes)
    print(message)
    return 0

if __name__ == "__main__":
    sys.exit(main())
