"""Exercise the shell policy used by the cache trust dispatch action."""

import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / ".github/actions/cache-trust-dispatch/action.yml"
SCRIPT = textwrap.dedent(ACTION.read_text().split("      run: |\n", 1)[1])
MAIN = "leanprover-community/mathlib4"
NIGHTLY = MAIN + "-nightly-testing"
SHA = "a" * 40


class DispatchTests(unittest.TestCase):
    def dispatch(self, repo, branch, host=None, ref_type="branch", sha=SHA):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output"
            env_file = Path(directory) / "env"
            result = subprocess.run(
                ["bash", "-euo", "pipefail", "-c", SCRIPT],
                env={**os.environ, "REPO": repo, "BRANCH": branch,
                     "HEAD_SHA": sha, "REF_TYPE": ref_type,
                     "GITHUB_REPOSITORY": host or repo,
                     "GITHUB_OUTPUT": str(output), "GITHUB_ENV": str(env_file)},
                text=True, capture_output=True,
            )
            values = dict(line.split("=", 1) for line in output.read_text().splitlines()) \
                if output.exists() else {}
            return result, values

    def test_all_nightly_branches_share_a_scoped_destination(self):
        for branch in ("nightly-testing", "nightly-testing-green", "staging", "trying",
                       "bump/nightly-2026-10-01", "batteries-pr-testing-1",
                       "lean-pr-testing-1", 'dev/$(exit 99)'):
            with self.subTest(branch=branch):
                result, values = self.dispatch(NIGHTLY, branch)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(values, {"primary": "nightly-testing",
                                         "read-chain": "master,nightly-testing",
                                         "repo-scope": SHA})

    def test_nightly_pr_into_mathlib_keeps_fork_trust(self):
        result, values = self.dispatch(NIGHTLY, "bump/nightly", host=MAIN)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values["primary"], "forks")
        self.assertEqual(values["read-chain"], "master,forks")
        self.assertEqual(values["repo-scope"], SHA)

    def test_public_cache_does_not_widen(self):
        for branch, ref_type in (("master", "branch"), ("staging", "branch"),
                                 ("v4.35.0", "tag")):
            result, values = self.dispatch(MAIN, branch, ref_type=ref_type)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(values, {"primary": "master", "read-chain": "", "repo-scope": ""})

    def test_canonical_development_branches_keep_fork_trust(self):
        for branch in ("trying", "ci-dev/cache"):
            result, values = self.dispatch(MAIN, branch)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(values, {"primary": "forks", "read-chain": "master,forks",
                                     "repo-scope": SHA})

    def test_scoped_uploads_reject_missing_or_invalid_sha(self):
        for sha in ("", "a" * 39, "A" * 40, "../master", SHA + "\nother=value"):
            result, values = self.dispatch(NIGHTLY, "nightly-testing", sha=sha)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(values, {})


if __name__ == "__main__":
    unittest.main()
