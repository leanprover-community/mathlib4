#!/usr/bin/env python3
"""Tests for ``extract_measure_theory_documentation.py``."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("extract_measure_theory_documentation.py")
SPEC = importlib.util.spec_from_file_location("extract_measure_theory_documentation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
EXTRACTOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = EXTRACTOR
SPEC.loader.exec_module(EXTRACTOR)


class ExtractMeasureTheoryDocumentationTest(unittest.TestCase):
    def test_extracts_all_comment_forms_but_not_strings(self) -> None:
        source = '''
-- line documentation
/- ordinary block -/
/-! module documentation -/
/-- declaration documentation -/
/- outer /- nested -/ block -/
@[to_additive /-- attribute documentation -/]
def quoted := "-- not a comment; /- neither is this -/"
def raw := r#"/- not a comment -/"#
'''
        comments = [comment.text.strip() for comment in EXTRACTOR.extract_comments(source)]
        self.assertEqual(
            comments,
            [
                "line documentation",
                "ordinary block",
                "module documentation",
                "declaration documentation",
                "outer  nested  block",
                "attribute documentation",
            ],
        )

    def test_cleans_code_and_links(self) -> None:
        cleaned = EXTRACTOR.clean_comment(
            "Read `MeasureTheory.foo` and [these words](https://example.com/a). "
            "See [MeasureTheory.bar](https://example.com/b), [reference prose][ref], "
            "<https://example.com/c>, and https://example.com/d."
        )
        self.assertEqual(cleaned, "Read  and these words. See , reference prose, , and .")

    def test_removes_fenced_and_malformed_code_spans(self) -> None:
        cleaned = EXTRACTOR.clean_comment(
            "Before.\n```lean\ndef code := 1\n```\nAfter `unfinished code\nStill prose."
        )
        self.assertEqual(cleaned, "Before.\nAfter \nStill prose.")

    def test_renders_sorted_file_boundaries(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source_root = Path(directory) / "MeasureTheory"
            source_root.mkdir()
            (source_root / "Z.lean").write_text("-- zebra\n", encoding="utf-8")
            (source_root / "A.lean").write_text(
                """/-
Copyright (c) 2026 Example Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Example Author
-/
-- ant
""",
                encoding="utf-8",
            )
            (source_root / "Empty.lean").write_text("def empty := 0\n", encoding="utf-8")

            corpus = EXTRACTOR.build_corpus(source_root)

        self.assertLess(corpus.index("BEGIN FILE: MeasureTheory/A.lean"),
                        corpus.index("BEGIN FILE: MeasureTheory/Empty.lean"))
        self.assertLess(corpus.index("BEGIN FILE: MeasureTheory/Empty.lean"),
                        corpus.index("BEGIN FILE: MeasureTheory/Z.lean"))
        self.assertIn("BEGIN FILE: MeasureTheory/Empty.lean", corpus)
        self.assertIn("ant", corpus)
        self.assertIn("zebra", corpus)
        self.assertNotIn("Copyright", corpus)
        self.assertNotIn("Example Author", corpus)

    def test_check_mode_does_not_write_missing_or_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            directory_path = Path(directory)
            source_root = directory_path / "MeasureTheory"
            source_root.mkdir()
            (source_root / "A.lean").write_text("-- ant\n", encoding="utf-8")
            output = directory_path / "comments.txt"
            command = [
                sys.executable,
                str(SCRIPT),
                "--source-root",
                str(source_root),
                "--output",
                str(output),
            ]

            missing = subprocess.run(command + ["--check"], check=False, capture_output=True, text=True)
            self.assertEqual(missing.returncode, 1)
            self.assertFalse(output.exists())

            subprocess.run(command, check=True)
            self.assertEqual(subprocess.run(command + ["--check"], check=False).returncode, 0)

            (source_root / "A.lean").write_text("-- aardvark\n", encoding="utf-8")
            previous_output = output.read_text(encoding="utf-8")
            stale = subprocess.run(command + ["--check"], check=False, capture_output=True, text=True)
            self.assertEqual(stale.returncode, 1)
            self.assertEqual(output.read_text(encoding="utf-8"), previous_output)


if __name__ == "__main__":
    unittest.main()
