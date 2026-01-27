#!/usr/bin/env python3

"""Verify that Mathlib version tags are published correctly and consistently.

This script checks that a given version tag (e.g., v4.24.1) is correctly
set up across all git remotes, GitHub, elan toolchains, and build cache.

Usage:
    # Verify a single tag
    python verify_version_tags.py v4.24.1

    # Verify all version tags
    python verify_version_tags.py --all

    # Verify all tags since a given version
    python verify_version_tags.py --since v4.20.0

Version tag formats supported:
    vX.Y.Z          (e.g., v4.24.1)
    vX.Y.Z-rcK      (e.g., v4.24.0-rc1)
    vX.Y.Z-patchM   (e.g., v4.24.1-patch1)
    vX.Y.Z-rcK-patchM (e.g., v4.24.0-rc1-patch2)

The script performs the following verification steps:
- Local/remote commit consistency across all git remotes
- GitHub tags page consistency via gh API
- Checkout tag to temporary directory
- lean-toolchain file matches expected version (sans -patchM suffix)
- Lean version (downloads toolchain via elan if needed, verifies Release build, checks commit SHA)
- Elan toolchain directory structure sanity check
- ProofWidgets toolchain consistency (warning only)
- Cache download verification (lake exe cache get)
- Build verification (lake build --no-build)
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from functools import total_ordering
from pathlib import Path
from typing import List, Optional, Tuple

# Unicode symbols (matching downstream-tags.py pattern)
TICK = "\u2705"   # Check mark button
CROSS = "\u274c"  # Cross mark
WARN = "\u26a0\ufe0f"   # Warning

MATHLIB_REPO = "leanprover-community/mathlib4"
GITHUB_URL = f"https://github.com/{MATHLIB_REPO}"

# Minimum Lean version that supports `lake --no-build build`
# Added in v4.2.0-rc2: https://github.com/leanprover/lean4/commit/f3de5eb1e8dc0708cd5b7983c282cace6e025957
MIN_NO_BUILD_VERSION = (4, 2, 0, 2)  # (major, minor, patch, rc) - rc2 or later

# Regex for version tag format
# Matches: v4.24.1, v4.24.0-rc1, v4.24.1-patch1, v4.24.0-rc1-patch2
VERSION_TAG_PATTERN = re.compile(
    r'^v(\d+)\.(\d+)\.(\d+)(?:-(rc(\d+)))?(?:-(patch(\d+)))?$'
)


@total_ordering
@dataclass
class VersionTag:
    """Parsed version tag components."""
    raw: str           # Original string like "v4.24.1-patch1"
    major: int         # 4
    minor: int         # 24
    patch: int         # 1
    rc: Optional[int]  # None or rc number (1, 2, ...)
    patch_suffix: Optional[int]  # None or patch number (1, 2, ...)

    @property
    def base_version(self) -> str:
        """Version without patch suffix, for lean-toolchain comparison.

        E.g., v4.24.1-patch1 -> v4.24.1
              v4.24.0-rc1-patch2 -> v4.24.0-rc1
        """
        base = f"v{self.major}.{self.minor}.{self.patch}"
        if self.rc is not None:
            base += f"-rc{self.rc}"
        return base

    def __lt__(self, other: 'VersionTag') -> bool:
        """Compare versions for sorting (--since flag)."""
        # Major.minor.patch comparison
        if (self.major, self.minor, self.patch) != (other.major, other.minor, other.patch):
            return (self.major, self.minor, self.patch) < (other.major, other.minor, other.patch)
        # RC versions sort before final versions (rc=None means final)
        self_rc = self.rc if self.rc is not None else float('inf')
        other_rc = other.rc if other.rc is not None else float('inf')
        if self_rc != other_rc:
            return self_rc < other_rc
        # Patch suffix comparison
        self_patch = self.patch_suffix if self.patch_suffix is not None else 0
        other_patch = other.patch_suffix if other.patch_suffix is not None else 0
        return self_patch < other_patch

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, VersionTag):
            return NotImplemented
        return (self.major, self.minor, self.patch, self.rc, self.patch_suffix) == \
               (other.major, other.minor, other.patch, other.rc, other.patch_suffix)

    def supports_no_build(self) -> bool:
        """Check if this version supports `lake --no-build build`.

        Added in v4.2.0-rc2.
        """
        # Compare (major, minor, patch, rc) where rc=None means final release
        # Final releases sort after all RCs, so we use a large number
        self_tuple = (self.major, self.minor, self.patch,
                      self.rc if self.rc is not None else 9999)
        min_tuple = MIN_NO_BUILD_VERSION  # (4, 2, 0, 2)
        return self_tuple >= min_tuple


@dataclass
class VerificationResult:
    """Result of a single verification step."""
    success: bool
    message: str
    warning: bool = False  # True if this is a warning, not a failure


def check_gh_installed() -> None:
    """Check if GitHub CLI (gh) is installed and accessible."""
    if not shutil.which('gh'):
        print("Error: GitHub CLI (gh) is not installed or not in PATH", file=sys.stderr)
        print("Please install it from https://cli.github.com/", file=sys.stderr)
        sys.exit(1)


def parse_version_tag(tag: str) -> Optional[VersionTag]:
    """Parse a version tag string into components.

    Returns None if the tag doesn't match the expected format.

    Examples:
        v4.24.1 -> VersionTag(major=4, minor=24, patch=1, rc=None, patch_suffix=None)
        v4.24.0-rc1 -> VersionTag(major=4, minor=24, patch=0, rc=1, patch_suffix=None)
        v4.24.1-patch1 -> VersionTag(major=4, minor=24, patch=1, rc=None, patch_suffix=1)
    """
    match = VERSION_TAG_PATTERN.match(tag)
    if not match:
        return None

    major = int(match.group(1))
    minor = int(match.group(2))
    patch = int(match.group(3))
    rc = int(match.group(5)) if match.group(5) else None
    patch_suffix = int(match.group(7)) if match.group(7) else None

    return VersionTag(
        raw=tag,
        major=major,
        minor=minor,
        patch=patch,
        rc=rc,
        patch_suffix=patch_suffix
    )


def run_cmd(cmd: List[str], cwd: Optional[str] = None,
            timeout: Optional[int] = None) -> Tuple[int, str, str]:
    """Run a command and return (returncode, stdout, stderr)."""
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=timeout
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return 1, "", "Command timed out"
    except Exception as e:
        return 1, "", str(e)


def get_all_version_tags() -> List[VersionTag]:
    """Fetch all version tags from GitHub."""
    code, stdout, stderr = run_cmd([
        'gh', 'api', '--paginate', f'repos/{MATHLIB_REPO}/git/refs/tags'
    ])

    if code != 0:
        print(f"Error fetching tags from GitHub: {stderr}", file=sys.stderr)
        return []

    try:
        tags_data = json.loads(stdout)
    except json.JSONDecodeError:
        print(f"Error parsing GitHub response", file=sys.stderr)
        return []

    version_tags = []
    for tag_ref in tags_data:
        ref = tag_ref.get('ref', '')
        tag_name = ref.replace('refs/tags/', '')
        parsed = parse_version_tag(tag_name)
        if parsed:
            version_tags.append(parsed)

    return sorted(version_tags)


def filter_tags_since(tags: List[VersionTag], since: VersionTag) -> List[VersionTag]:
    """Filter tags to only those >= since version."""
    return [t for t in tags if t >= since]


# ============================================================================
# Verification Steps
# ============================================================================

def verify_local_remote_consistency(tag: str) -> VerificationResult:
    """Verify tag points to same commit locally and on the main repo.

    Also warns if any other configured remote has the tag pointing to a different commit.
    """
    # Get local SHA
    code, stdout, _ = run_cmd(['git', 'rev-parse', tag])
    if code != 0:
        # Tag not found locally - this is expected when running from release_checklist.py
        # which uses a shallow clone without tags. The GitHub check (verify_github_tag)
        # verifies the tag exists remotely, so this is not an error or warning.
        return VerificationResult(
            True,
            f"Skipped (tag not in local checkout; GitHub check will verify)"
        )
    local_sha = stdout.strip()

    # Get all remotes and their URLs
    code, stdout, _ = run_cmd(['git', 'remote'])
    if code != 0:
        return VerificationResult(False, "Failed to enumerate git remotes")
    remotes = [r.strip() for r in stdout.splitlines() if r.strip()]

    # Find which remote(s) point to the main repo
    # Match leanprover-community/mathlib4 but not mathlib4-nightly-testing etc.
    # Matches common git URL formats: https://, git@, git://
    main_repo_pattern = re.compile(
        r'(?:https://|git@|git://)[^/]+[:/]leanprover-community/mathlib4(?:\.git)?$'
    )
    main_repo_remotes = []
    other_remotes = []
    for remote in remotes:
        code, url, _ = run_cmd(['git', 'remote', 'get-url', remote])
        if code == 0:
            url = url.strip()
            if main_repo_pattern.search(url):
                main_repo_remotes.append(remote)
            else:
                other_remotes.append(remote)

    if not main_repo_remotes:
        return VerificationResult(False, "No remote pointing to leanprover-community/mathlib4 found")

    # Check main repo remote(s) - these must have the tag with correct SHA
    for remote in main_repo_remotes:
        code, stdout, _ = run_cmd(['git', 'ls-remote', '--refs', remote, f'refs/tags/{tag}'])
        if code != 0 or not stdout.strip():
            return VerificationResult(False, f"Tag not found on {remote} (main repo)")
        remote_sha = stdout.split()[0]
        if remote_sha != local_sha:
            return VerificationResult(
                False,
                f"SHA mismatch on {remote}: {remote_sha[:12]} (local: {local_sha[:12]})"
            )

    # Check other remotes - warn if tag exists but points to wrong commit
    warnings = []
    for remote in other_remotes:
        code, stdout, _ = run_cmd(['git', 'ls-remote', '--refs', remote, f'refs/tags/{tag}'])
        if code == 0 and stdout.strip():
            remote_sha = stdout.split()[0]
            if remote_sha != local_sha:
                warnings.append(f"{remote}: {remote_sha[:12]}")

    if warnings:
        return VerificationResult(
            True,
            f"OK on main repo ({local_sha[:12]}), but mismatched on: {'; '.join(warnings)}",
            warning=True
        )

    return VerificationResult(True, f"Consistent: {local_sha[:12]}")


def verify_github_tag(tag: str) -> VerificationResult:
    """Verify tag appears at GitHub with same commit using gh API."""
    # Get local SHA for comparison
    code, stdout, _ = run_cmd(['git', 'rev-parse', tag])
    local_sha = stdout.strip() if code == 0 else None

    # Query GitHub API
    code, stdout, stderr = run_cmd([
        'gh', 'api', f'repos/{MATHLIB_REPO}/git/refs/tags/{tag}'
    ])

    if code != 0:
        return VerificationResult(False, f"Tag {tag} not found on GitHub")

    try:
        data = json.loads(stdout)
        github_sha = data['object']['sha']
    except (json.JSONDecodeError, KeyError) as e:
        return VerificationResult(False, f"Failed to parse GitHub response: {e}")

    if local_sha and github_sha != local_sha:
        return VerificationResult(
            False,
            f"GitHub SHA {github_sha[:12]} differs from local {local_sha[:12]}"
        )

    return VerificationResult(True, f"Found on GitHub: {github_sha[:12]}")


def verify_checkout(tag: str, checkout_dir: str) -> VerificationResult:
    """Clone/checkout the tag into a temporary directory."""
    code, stdout, stderr = run_cmd([
        'git', 'clone', '--depth', '1', '--branch', tag,
        f'{GITHUB_URL}.git', checkout_dir
    ], timeout=120)

    if code != 0:
        return VerificationResult(False, f"Failed to checkout: {stderr.strip()[:200]}")

    return VerificationResult(True, f"Checked out to {checkout_dir}")


def verify_lean_toolchain(tag: str, checkout_dir: str) -> VerificationResult:
    """Verify lean-toolchain file uses correct version (strip -patchM suffix)."""
    parsed = parse_version_tag(tag)
    if not parsed:
        return VerificationResult(False, f"Cannot parse version tag: {tag}")

    toolchain_path = Path(checkout_dir) / 'lean-toolchain'
    if not toolchain_path.exists():
        return VerificationResult(False, "lean-toolchain file not found")

    content = toolchain_path.read_text().strip()
    expected_prefix = "leanprover/lean4:"
    if not content.startswith(expected_prefix):
        return VerificationResult(False, f"Unexpected toolchain format: {content}")

    toolchain_version = content[len(expected_prefix):]
    expected_version = parsed.base_version

    if toolchain_version != expected_version:
        return VerificationResult(
            False,
            f"Toolchain {toolchain_version} doesn't match expected {expected_version}"
        )

    return VerificationResult(True, content)




def verify_elan_toolchain(tag: str, checkout_dir: str) -> VerificationResult:
    """Check that the actual lean binary path contains the expected version in its path."""
    parsed = parse_version_tag(tag)
    if not parsed:
        return VerificationResult(False, f"Cannot parse version tag: {tag}")

    expected_version = parsed.base_version

    # Get the actual path to the lean binary that lake env would use
    code, stdout, stderr = run_cmd(
        ['lake', 'env', 'printenv', 'LEAN'],
        cwd=checkout_dir,
        timeout=60
    )

    # Fallback: try which lean in lake env
    if code != 0 or not stdout.strip():
        code, stdout, stderr = run_cmd(
            ['lake', 'env', 'which', 'lean'],
            cwd=checkout_dir,
            timeout=60
        )

    if code != 0 or not stdout.strip():
        return VerificationResult(False, f"Cannot determine lean binary path")

    lean_path = stdout.strip()

    # Parse version from the path
    # Expected path format: ~/.elan/toolchains/leanprover--lean4---vX.Y.Z(-rcK)?/bin/lean
    path_match = re.search(r'leanprover--lean4---(v[\d.]+(?:-rc\d+)?)', lean_path)
    if not path_match:
        return VerificationResult(
            False,
            f"Cannot parse version from lean path: {lean_path}"
        )

    path_version = path_match.group(1)
    if path_version != expected_version:
        return VerificationResult(
            False,
            f"Path version {path_version} doesn't match expected {expected_version}"
        )

    # Extract just the toolchain directory for display
    toolchain_match = re.search(r'(\.elan/toolchains/[^/]+)', lean_path)
    toolchain_display = toolchain_match.group(1) if toolchain_match else lean_path

    return VerificationResult(True, f"~/{toolchain_display}/")


def get_lean_release_commit(version: str) -> Optional[str]:
    """Get the commit SHA for a Lean release tag from GitHub.

    Args:
        version: Version string like "v4.24.1" or "v4.0.0-rc2"

    Returns:
        The commit SHA, or None if not found.
    """
    code, stdout, stderr = run_cmd([
        'gh', 'api', f'repos/leanprover/lean4/git/refs/tags/{version}'
    ])

    if code != 0:
        return None

    try:
        data = json.loads(stdout)
        obj_type = data['object']['type']
        sha = data['object']['sha']

        # If it's an annotated tag, we need to dereference it to get the commit
        if obj_type == 'tag':
            code, stdout, stderr = run_cmd([
                'gh', 'api', f'repos/leanprover/lean4/git/tags/{sha}'
            ])
            if code == 0:
                tag_data = json.loads(stdout)
                sha = tag_data['object']['sha']

        return sha
    except (json.JSONDecodeError, KeyError):
        return None


def verify_lean_version_string(tag: str, checkout_dir: str) -> VerificationResult:
    """Verify Lean version string using lean --version.

    This also triggers elan to download the toolchain if needed.

    Checks:
    1. Version number matches (without -rcK suffix, which lean --version omits)
    2. Output contains "Release" (not a dev build)
    3. Commit SHA matches the release tag on leanprover/lean4
    """
    parsed = parse_version_tag(tag)
    if not parsed:
        return VerificationResult(False, f"Cannot parse version tag: {tag}")

    # Use lake env lean --version to get the version string
    # This also triggers elan to download the toolchain if needed
    # Stream stderr with indentation so user sees download progress
    proc = None
    try:
        proc = subprocess.Popen(
            ['lake', 'env', 'lean', '--version'],
            cwd=checkout_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            # Read stderr line by line and print with indentation
            stderr_lines = []
            for line in proc.stderr:
                print(f"       {line}", end="", flush=True)
                stderr_lines.append(line)
            stdout, _ = proc.communicate(timeout=300)
            code = proc.returncode
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()  # Clean up zombie process
            return VerificationResult(False, "Timed out (toolchain download?)")
        except Exception:
            # Ensure process is terminated if something goes wrong during stderr reading
            if proc.poll() is None:  # Process still running
                proc.kill()
                proc.wait()
            raise
    except Exception as e:
        return VerificationResult(False, f"Failed: {e}")

    if code != 0:
        return VerificationResult(False, f"Failed to get version (exit code {code})")

    version_output = stdout.strip().split('\n')[0] if stdout.strip() else ""

    # Check that output contains "Release"
    if 'Release' not in version_output:
        return VerificationResult(
            False,
            f"Not a release build: {version_output}"
        )

    # Check version number (without -rcK suffix, which lean --version omits for RCs)
    # For v4.24.1 -> expect "4.24.1"
    # For v4.0.0-rc2 -> expect "4.0.0" (lean --version doesn't show -rc suffix)
    expected_version = f"{parsed.major}.{parsed.minor}.{parsed.patch}"
    if expected_version not in version_output:
        return VerificationResult(
            False,
            f"Version mismatch: got {version_output}, expected to contain {expected_version}"
        )

    # Extract commit SHA from output
    # Format: "Lean (version 4.0.0, commit 216d2460e0ad, Release)"
    commit_match = re.search(r'commit ([0-9a-f]+)', version_output)
    if not commit_match:
        return VerificationResult(
            False,
            f"Cannot extract commit SHA from: {version_output}"
        )
    reported_commit = commit_match.group(1)

    # Verify commit SHA matches the Lean release tag
    expected_commit = get_lean_release_commit(parsed.base_version)
    if expected_commit is None:
        return VerificationResult(
            False,
            f"Cannot find Lean release tag {parsed.base_version} on GitHub"
        )

    # Compare (reported_commit may be abbreviated)
    if not expected_commit.startswith(reported_commit):
        return VerificationResult(
            False,
            f"Commit mismatch: lean reports {reported_commit}, "
            f"but {parsed.base_version} tag points to {expected_commit[:12]}"
        )

    # Print the commit verification on a separate line
    print(f"  {TICK} Lean version: {version_output}")
    print(f"  {TICK} Lean commit: {reported_commit} matches leanprover/lean4 tag {parsed.base_version}")

    return VerificationResult(True, "")


def has_proofwidgets_dependency(checkout_dir: str) -> bool:
    """Check if proofwidgets is listed in lake-manifest.json."""
    manifest_path = Path(checkout_dir) / 'lake-manifest.json'
    if not manifest_path.exists():
        return False

    try:
        with open(manifest_path) as f:
            manifest = json.load(f)
        packages = manifest.get('packages', [])
        for pkg in packages:
            # Handle different manifest formats:
            # - Newer format: {"git": {"name": "proofwidgets", ...}}
            # - Older format might have name at top level
            name = pkg.get('name', '')
            if not name:
                # Check nested in git/path package types
                for pkg_type in ['git', 'path']:
                    if pkg_type in pkg:
                        name = pkg[pkg_type].get('name', '')
                        break
            if name.lower() == 'proofwidgets':
                return True
        return False
    except (json.JSONDecodeError, KeyError):
        return False


def get_packages_dir(checkout_dir: str) -> Path:
    """Get the packages directory from lake-manifest.json, with fallbacks.

    Earlier versions used 'lake-packages', newer versions use '.lake/packages'.
    The manifest's 'packagesDir' field tells us which one to use.
    """
    manifest_path = Path(checkout_dir) / 'lake-manifest.json'
    if manifest_path.exists():
        try:
            with open(manifest_path) as f:
                manifest = json.load(f)
            packages_dir = manifest.get('packagesDir')
            if packages_dir:
                return Path(checkout_dir) / packages_dir
        except (json.JSONDecodeError, KeyError):
            pass

    # Fallback: check both locations
    new_path = Path(checkout_dir) / '.lake' / 'packages'
    old_path = Path(checkout_dir) / 'lake-packages'
    if new_path.exists():
        return new_path
    if old_path.exists():
        return old_path
    # Default to new path if neither exists yet
    return new_path


def verify_proofwidgets_toolchain(checkout_dir: str) -> Optional[VerificationResult]:
    """Verify ProofWidgets lean-toolchain matches root (WARNING only if mismatch).

    Returns None if proofwidgets is not a dependency (skip this check).
    """
    # Skip if proofwidgets is not in lake-manifest.json
    if not has_proofwidgets_dependency(checkout_dir):
        return None

    root_toolchain = Path(checkout_dir) / 'lean-toolchain'
    packages_dir = get_packages_dir(checkout_dir)
    pw_toolchain = packages_dir / 'proofwidgets' / 'lean-toolchain'

    if not root_toolchain.exists():
        return VerificationResult(True, "Root lean-toolchain not found", warning=True)

    if not pw_toolchain.exists():
        return VerificationResult(
            True,
            "ProofWidgets not yet downloaded (run cache get first)",
            warning=True
        )

    root_content = root_toolchain.read_text().strip()
    pw_content = pw_toolchain.read_text().strip()

    if root_content != pw_content:
        return VerificationResult(
            True,  # Warning, not failure
            f"ProofWidgets toolchain mismatch: {pw_content} vs {root_content}",
            warning=True
        )

    return VerificationResult(True, "matches root")


def verify_cache_download(checkout_dir: str) -> VerificationResult:
    """Run lake exe cache get."""
    code, stdout, stderr = run_cmd(
        ['lake', 'exe', 'cache', 'get'],
        cwd=checkout_dir,
        timeout=600  # 10 minutes for cache download
    )

    if code != 0:
        return VerificationResult(False, f"Cache download failed: {stderr.strip()[:200]}")

    return VerificationResult(True, "Cache downloaded successfully")


def verify_build(tag: str, checkout_dir: str) -> VerificationResult:
    """Run lake --no-build build (should succeed if everything cached).

    For versions before v4.2.0-rc2, --no-build is not available, so we skip with a warning.
    """
    parsed = parse_version_tag(tag)
    if not parsed:
        return VerificationResult(False, f"Cannot parse version tag: {tag}")

    if not parsed.supports_no_build():
        return VerificationResult(
            True,
            f"`--no-build` not available prior to v4.2.0-rc2, skipping build",
            warning=True
        )

    code, stdout, stderr = run_cmd(
        ['lake', '--no-build', 'build'],
        cwd=checkout_dir,
        timeout=120
    )

    if code != 0:
        return VerificationResult(False, "Build failed")

    return VerificationResult(True, "--no-build succeeded")


# ============================================================================
# Main verification orchestration
# ============================================================================

def print_result(step_name: str, result: VerificationResult) -> None:
    """Print a single verification step result."""
    if result.warning:
        symbol = WARN
    elif result.success:
        symbol = TICK
    else:
        symbol = CROSS
    print(f"  {symbol} {step_name}: {result.message}")


def verify_tag(tag: str) -> Tuple[bool, bool]:
    """Run all verification steps for a single tag.

    Returns:
        (has_errors, has_warnings): Tuple of booleans indicating if there were errors or warnings.
    """
    print(f"\nVerifying tag: {tag}")
    print("-" * 50)

    has_errors = False
    has_warnings = False

    result = verify_local_remote_consistency(tag)
    print_result("Local/remote consistency", result)
    if not result.success:
        has_errors = True
    elif result.warning:
        has_warnings = True

    result = verify_github_tag(tag)
    print_result("GitHub tag", result)
    if not result.success:
        has_errors = True
    elif result.warning:
        has_warnings = True

    with tempfile.TemporaryDirectory() as tmpdir:
        checkout_dir = os.path.join(tmpdir, 'mathlib4')

        result = verify_checkout(tag, checkout_dir)
        print_result("Checkout", result)
        if not result.success:
            has_errors = True
            return has_errors, has_warnings  # Can't continue without checkout
        elif result.warning:
            has_warnings = True

        result = verify_lean_toolchain(tag, checkout_dir)
        print_result("lean-toolchain", result)
        if not result.success:
            has_errors = True
        elif result.warning:
            has_warnings = True

        # This may trigger toolchain download and dependency fetching, which streams to stderr
        # The function prints its own success output, so we only print on failure
        print("  ... Lean version (may download toolchain and Mathlib dependencies):", flush=True)
        result = verify_lean_version_string(tag, checkout_dir)
        if not result.success:
            print_result("Lean version", result)
            has_errors = True
        elif result.warning:
            has_warnings = True

        result = verify_elan_toolchain(tag, checkout_dir)
        print_result("Elan toolchain", result)
        if not result.success:
            has_errors = True
        elif result.warning:
            has_warnings = True

        result = verify_proofwidgets_toolchain(checkout_dir)
        if result is not None:
            print_result("ProofWidgets toolchain", result)
            if not result.success:
                has_errors = True
            elif result.warning:
                has_warnings = True

        result = verify_cache_download(checkout_dir)
        print_result("Cache download", result)
        if not result.success:
            has_errors = True
        elif result.warning:
            has_warnings = True

        result = verify_build(tag, checkout_dir)
        print_result("Build verification", result)
        if not result.success:
            has_errors = True
        elif result.warning:
            has_warnings = True

    return has_errors, has_warnings


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Verify Mathlib version tags are published correctly.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s v4.24.1          Verify a single tag
  %(prog)s --all            Verify all version tags
  %(prog)s --since v4.20.0  Verify tags since v4.20.0
"""
    )
    parser.add_argument(
        'tag',
        nargs='?',
        help='Version tag to verify (e.g., v4.24.1)'
    )
    parser.add_argument(
        '--all',
        action='store_true',
        help='Verify all version tags from the repository'
    )
    parser.add_argument(
        '--since',
        metavar='VERSION',
        help='Verify all tags since the given version (e.g., v4.20.0)'
    )

    args = parser.parse_args()

    # Validate arguments
    if args.all and args.since:
        print("Error: Cannot use --all and --since together", file=sys.stderr)
        sys.exit(1)

    if args.all and args.tag:
        print("Error: Cannot specify a tag with --all", file=sys.stderr)
        sys.exit(1)

    if args.since and args.tag:
        print("Error: Cannot specify a tag with --since", file=sys.stderr)
        sys.exit(1)

    if not args.all and not args.since and not args.tag:
        parser.print_help()
        sys.exit(1)

    # Check prerequisites
    check_gh_installed()

    # Determine which tags to verify
    tags_to_verify: List[str] = []

    if args.tag:
        # Single tag mode
        parsed = parse_version_tag(args.tag)
        if not parsed:
            print(f"Error: Invalid version tag format: {args.tag}", file=sys.stderr)
            print("Expected format: vX.Y.Z, vX.Y.Z-rcK, vX.Y.Z-patchM, or vX.Y.Z-rcK-patchM",
                  file=sys.stderr)
            sys.exit(1)
        tags_to_verify = [args.tag]

    elif args.all:
        # All tags mode
        print("Fetching all version tags from GitHub...")
        all_tags = get_all_version_tags()
        if not all_tags:
            print("Error: No version tags found", file=sys.stderr)
            sys.exit(1)
        tags_to_verify = [t.raw for t in all_tags]
        print(f"Found {len(tags_to_verify)} version tag(s)")

    elif args.since:
        # Since version mode
        since_parsed = parse_version_tag(args.since)
        if not since_parsed:
            print(f"Error: Invalid version tag format for --since: {args.since}",
                  file=sys.stderr)
            sys.exit(1)

        print(f"Fetching version tags since {args.since} from GitHub...")
        all_tags = get_all_version_tags()
        if not all_tags:
            print("Error: No version tags found", file=sys.stderr)
            sys.exit(1)

        filtered = filter_tags_since(all_tags, since_parsed)
        if not filtered:
            print(f"Error: No version tags found >= {args.since}", file=sys.stderr)
            sys.exit(1)

        tags_to_verify = [t.raw for t in filtered]
        print(f"Found {len(tags_to_verify)} version tag(s) since {args.since}")

    # Verify tags
    passed = 0
    failed = 0
    failed_tags: List[str] = []
    any_errors = False
    any_warnings = False

    for tag in tags_to_verify:
        has_errors, has_warnings = verify_tag(tag)
        if has_errors or has_warnings:
            failed += 1
            failed_tags.append(tag)
            if has_errors:
                any_errors = True
            if has_warnings:
                any_warnings = True
        else:
            passed += 1

    # Print summary for multi-tag modes
    if len(tags_to_verify) > 1:
        print("\n" + "=" * 50)
        print("SUMMARY")
        print("=" * 50)

        # Build set of all tags for checking if patches exist
        all_parsed = [parse_version_tag(t) for t in tags_to_verify]
        all_parsed = [p for p in all_parsed if p is not None]

        # Determine error vs warning for each failed tag
        errors = []
        warnings = []

        for tag in failed_tags:
            parsed = parse_version_tag(tag)
            if not parsed:
                errors.append(tag)
                continue

            # Release candidates are always warnings
            if parsed.rc is not None and parsed.patch_suffix is None:
                warnings.append(tag)
                continue

            # Check if this stable/patch version has a later patch
            has_later_patch = any(
                p.major == parsed.major and
                p.minor == parsed.minor and
                p.patch == parsed.patch and
                p.rc == parsed.rc and
                (p.patch_suffix or 0) > (parsed.patch_suffix or 0)
                for p in all_parsed
            )

            if has_later_patch:
                warnings.append(tag)
            else:
                errors.append(tag)

        # Print one line per tag
        for tag in tags_to_verify:
            if tag in errors:
                print(f"  {CROSS} {tag}")
            elif tag in warnings:
                print(f"  {WARN} {tag}")
            else:
                print(f"  {TICK} {tag}")

        print()
        if errors:
            print(f"Errors: {len(errors)}, Warnings: {len(warnings)}, Passed: {passed}/{passed + failed}")
        elif warnings:
            print(f"Warnings: {len(warnings)}, Passed: {passed}/{passed + failed}")
        else:
            print(f"Passed: {passed}/{passed + failed}")

        # Multi-tag mode: Exit with error only if there are actual errors (not just warnings)
        sys.exit(0 if not errors else 1)
    else:
        # Single tag mode: Exit with error if there are errors OR warnings
        sys.exit(0 if not (any_errors or any_warnings) else 1)


if __name__ == "__main__":
    main()
