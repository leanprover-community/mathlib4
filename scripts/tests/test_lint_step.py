"""Check the CI lint step's failure and retry behavior without running Lean."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


WORKFLOW = Path(__file__).resolve().parents[2] / '.github/workflows/build_template.yml'


def lint_script():
    step = WORKFLOW.read_text().split('      - name: lint mathlib\n', 1)[1]
    step = step.split('      - name:', 1)[0]
    script = step.split('        run: |\n', 1)[1]
    return '\n'.join(line[10:] for line in script.splitlines() if line.startswith('          '))


class LintStepTests(unittest.TestCase):
    def run_lint(self, statuses, message=''):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'pr-branch/.lake').mkdir(parents=True)
            commands = root / 'bin'
            commands.mkdir()
            # The timeout shim replaces the whole command below it. Its exits model
            # linter errors and timeouts without relying on elapsed time or Lean.
            timeout = commands / 'timeout'
            timeout.write_text('''#!/usr/bin/env bash
set -eu
attempt=$(cat .lake/calls 2>/dev/null || echo 0)
attempt=$((attempt + 1))
printf '%s' "$attempt" > .lake/calls
printf '%s\\n' "$MOCK_MESSAGE"
read -ra statuses <<< "$MOCK_STATUSES"
exit "${statuses[$((attempt - 1))]}"
''')
            timeout.chmod(0o755)
            env = dict(os.environ, PATH=f'{commands}:{os.environ["PATH"]}',
                       MOCK_STATUSES=' '.join(map(str, statuses)), MOCK_MESSAGE=message)
            result = subprocess.run(['bash', '-euo', 'pipefail', '-c', lint_script()],
                                    cwd=root, env=env, capture_output=True, text=True)
            calls = int((root / 'pr-branch/.lake/calls').read_text())
            return result.returncode, calls

    def test_success(self):
        self.assertEqual(self.run_lint([0]), (0, 1))

    def test_lint_failure_is_not_retried_or_hidden(self):
        self.assertEqual(self.run_lint([1]), (1, 1))
        self.assertEqual(self.run_lint([2]), (2, 1))

    def test_retry_only_timeouts(self):
        self.assertEqual(self.run_lint([124, 0]), (0, 2))
        self.assertEqual(self.run_lint([124, 124]), (124, 2))
        self.assertEqual(self.run_lint([124, 1]), (1, 2))

    def test_outdated_branch_fails(self):
        self.assertEqual(self.run_lint([2], 'no lint driver configured'), (1, 1))


if __name__ == '__main__':
    unittest.main()
