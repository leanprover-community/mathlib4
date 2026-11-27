"""Run with `python3 scripts/tests/fix_long_lines.py`."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from fix_long_lines import fix_line


class FixLongLinesTest(unittest.TestCase):
    def test_commas_inside_literals_and_comments(self):
        prose = "first part, " + "second part " * 10
        for prefix, suffix in [
            ('def s := "', '"'),
            ('def s := "escaped \\"', '"'),
            ('def s := "first line\n', '"'),
            ('def s := r##"a " and "#\n', '"##'),
            ('def s := s!"{"a" ++ "', '"}"'),
            ("def «", "» := 1"),
            ("def x := 1 -- ", ""),
            ("/- outer /- inner -/\n", " -/"),
        ]:
            with self.subTest(prefix=prefix):
                source = prefix + prose + suffix + "\n"
                self.assertEqual(fix_line(source, 1 + prefix.count("\n")), source)

    def test_uses_a_code_comma_before_a_string(self):
        item = '"first part, ' + 'second part ' * 10 + '"'
        self.assertEqual(fix_line('def xs := ["one", ' + item + ']\n', 1),
                         'def xs := ["one",\n  ' + item + ']\n')

    def test_wraps_ordinary_code_after_a_block_comment(self):
        prefix = '/- outer " /- inner -/\n-/\n'
        items = "1, " * 33
        line = "  [" + items + "2]\n"
        cut = line.rfind(",", 0, 100) + 1
        self.assertEqual(fix_line(prefix + line, 3),
                         prefix + line[:cut] + "\n    " + line[cut:].lstrip())

    def test_closing_delimiters_past_column_100(self):
        prefix = " " * 80 + "def c : Char :=   '"
        self.assertEqual(len(prefix), 99)
        line = prefix + ",' -- padding\n"
        self.assertEqual(fix_line(line, 1), line)

        prefix = 'def s := "first, '
        line = prefix.ljust(99) + '\\"end"\n'
        self.assertEqual(fix_line(line, 1), line)


if __name__ == "__main__":
    unittest.main()
