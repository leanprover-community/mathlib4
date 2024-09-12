#!/usr/bin/env python3
"""
Lint a file or files from mathlib for style.

Sample usage:

    $ ./scripts/lint-style.py $(find Mathlib -name '*.lean')

which will lint all of the Lean files in the specified directories.

The resulting error output will contain one line for each style error
encountered that isn't in the list of allowed / ignored style exceptions.

Paths with no errors will not appear in the output, and the script will
exit with successful return code if there are no errors encountered in
any provided paths.

Paths emitted in the output will match the paths provided on the
command line for any files containing errors -- in particular, linting
a relative path (like ``Mathlib/Foo/Bar.lean``) will produce errors
that contain the relative path, whilst linting absolute paths (like
``/root/mathlib4/Mathlib/Foo/Bar.lean``) will produce errors with the
absolute path.

The linters in this script are gradually being rewritten in Lean.
Do not add new linters here; please write them in Lean instead.

To run all style linters, run `lake exe lint-style`.
"""

# TODO: This is adapted from the linter for mathlib3. It should be rewritten in Lean.

from pathlib import Path
import sys
import re
import shutil

ERR_MOD = 2 # module docstring
ERR_IBY = 11 # isolated by
ERR_IWH = 22 # isolated where
ERR_CLN = 16 # line starts with a colon
ERR_IND = 17 # second line not correctly indented
ERR_ARR = 18 # space after "←"
ERR_NSP = 20 # non-terminal simp

exceptions = []
new_exceptions = False


def annotate_comments(enumerate_lines):
    """
    Take a list of tuples of enumerated lines of the form
    (line_number, line, ...)
    and return a list of
    (line_number, line, ..., True/False)
    where lines have True attached when they are in comments.
    """
    nesting_depth = 0 # We're in a comment when `nesting_depth > 0`.
    starts_in_comment = False # Whether we're in a comment when starting the line.
    for line_nr, line, *rem in enumerate_lines:
        # We assume multiline comments do not begin or end within single-line comments.
        if line == "\n" or line.lstrip().startswith("--"):
            yield line_nr, line, *rem, True
            continue
        # We assume that "/-/" and "-/-" never occur outside of "--" comments.
        # We assume that we do not encounter "... -/ <term> /- ...".
        # We also don't account for "/-" and "-/" appearing in strings.
        starts_in_comment = (nesting_depth > 0)
        nesting_depth = nesting_depth + line.count("/-") - line.count("-/")
        in_comment = (starts_in_comment or line.lstrip().startswith("/-")) and \
            (nesting_depth > 0 or line.rstrip().endswith("-/"))
        yield line_nr, line, *rem, in_comment

def annotate_strings(enumerate_lines):
    """
    Take a list of tuples of enumerated lines of the form
    (line_number, line, ...)
    and return a list of
    (line_number, line, ..., True/False)
    where lines have True attached when they are in strings.
    """
    in_string = False
    in_comment = False
    for line_nr, line, *rem in enumerate_lines:
        # ignore comment markers inside string literals
        if not in_string:
            if "/-" in line:
                in_comment = True
            if "-/" in line:
                in_comment = False
        # ignore quotes inside comments
        if not in_comment:
            # crude heuristic: if the number of non-escaped quote signs is odd,
            # we're starting / ending a string literal
            if line.count("\"") - line.count("\\\"") % 2 == 1:
                in_string = not in_string
            # if there are quote signs in this line,
            # a string literal probably begins and / or ends here,
            # so we skip this line
            if line.count("\"") > 0:
                yield line_nr, line, *rem, True
                continue
            if in_string:
                yield line_nr, line, *rem, True
                continue
        yield line_nr, line, *rem, False


def four_spaces_in_second_line(lines, path):
    # TODO: also fix the space for all lines before ":=", right now we only fix the line after
    # the first line break
    errors = []
    # We never alter the first line, as it does not occur as next_line in the iteration over the
    # zipped lines below, hence we add it here
    newlines = [lines[0]]
    annotated_lines = list(annotate_comments(lines))
    for (_, line, is_comment), (next_line_nr, next_line, _) in zip(annotated_lines,
                                                                   annotated_lines[1:]):
        # Check if the current line matches "(lemma|theorem) .* :"
        new_next_line = next_line
        if (not is_comment) and re.search(r"^(protected )?(def|lemma|theorem) (?!.*:=).*(where)?$",
                                          line):
            # Calculate the number of spaces before the first non-space character in the next line
            stripped_next_line = next_line.lstrip()
            if not (next_line == '\n' or next_line.startswith("#") or stripped_next_line.startswith("--")):
                num_spaces = len(next_line) - len(stripped_next_line)
                # The match with "| " could potentially match with a different usage of the same
                # symbol, e.g. some sort of norm. In that case a space is not necessary, so
                # looking for "| " should be enough.
                if stripped_next_line.startswith("| ") or line.endswith("where\n"):
                    # Check and fix if the number of leading space is not 2
                    if num_spaces != 2:
                        errors += [(ERR_IND, next_line_nr, path)]
                        new_next_line = ' ' * 2 + stripped_next_line
                # Check and fix if the number of leading spaces is not 4
                else:
                    if num_spaces != 4:
                        errors += [(ERR_IND, next_line_nr, path)]
                        new_next_line = ' ' * 4 + stripped_next_line
        newlines.append((next_line_nr, new_next_line))
    return errors, newlines

flexible_tactics = ["rfl", "ring", "aesop", "norm_num", "positivity", "abel", "omega", "linarith", "nlinarith"]

def nonterminal_simp_check(lines, path):
    errors = []
    newlines = []
    annotated_lines = list(annotate_comments(lines))
    for (line_nr, line, is_comment), (_, next_line, _) in zip(annotated_lines,
                                                              annotated_lines[1:]):
        # Check if the current line matches whitespace followed by "simp"
        new_line = line
        # TODO it would be better to use a regex like r"^\s*simp( \[.*\])?( at .*)?$" and thereby
        # catch all possible simp invocations. Adding this will require more initial cleanup or
        # nolint.
        if (not is_comment) and re.search(r"^\s*simp$", line):
            # Calculate the number of spaces before the first non-space character in the line
            num_spaces = len(line) - len(line.lstrip())
            # Calculate the number of spaces before the first non-space character in the next line
            stripped_next_line = next_line.lstrip()

            if not (next_line == '\n' or next_line.startswith("#") or stripped_next_line.startswith("--") or any(f in next_line for f in flexible_tactics)):
                num_next_spaces = len(next_line) - len(stripped_next_line)
                # Check if the number of leading spaces is the same
                if num_spaces == num_next_spaces:
                    # If so, the simp is nonterminal
                    errors += [(ERR_NSP, line_nr, path)]
                    new_line = line.replace("simp", "simp?")
        newlines.append((line_nr, new_line))
    newlines.append(lines[-1])
    return errors, newlines

def import_only_check(lines, path):
    for _, line, is_comment in annotate_comments(lines):
        if is_comment:
            continue
        imports = line.split()
        if imports[0] == "#align_import":
            continue
        if imports[0] != "import":
            return False
    return True

def regular_check(lines, path):
    errors = []
    copy_started = False
    copy_done = False
    for line_nr, line in lines:
        if not copy_started and line == "\n":
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            continue
        if copy_started and not copy_done:
            if line == "-/\n":
                copy_done = True
            continue
        if copy_done and line == "\n":
            continue
        words = line.split()
        if words[0] != "import" and words[0] != "--" and words[0] != "/-!" and words[0] != "#align_import":
            errors += [(ERR_MOD, line_nr, path)]
            break
        if words[0] == "/-!":
            break
    return errors, lines

def isolated_by_dot_semicolon_check(lines, path):
    errors = []
    newlines = []
    for line_nr, line in lines:
        if line.strip() == "by":
            # We excuse those "by"s following a comma or ", fun ... =>", since generally hanging "by"s
            # should not be used in the second or later arguments of a tuple/anonymous constructor
            # See https://github.com/leanprover-community/mathlib4/pull/3825#discussion_r1186702599
            prev_line = lines[line_nr - 2][1].rstrip()
            if not prev_line.endswith(",") and not re.search(", fun [^,]* (=>|↦)$", prev_line):
                errors += [(ERR_IBY, line_nr, path)]
        elif line.lstrip().startswith("by "):
            # We also error if the previous line ends on := and the current line starts with "by ".
            prev_line = newlines[-1][1].rstrip()
            if prev_line.endswith(":="):
                # If the previous line is short enough, we can suggest an auto-fix.
                # Future: error also if it is not: currently, mathlib contains about 30 such
                # instances which are not obvious to fix.
                if len(prev_line) <= 97:
                    errors += [(ERR_IBY, line_nr, path)]
                    newlines[-1] = (line_nr - 1, prev_line + " by\n")
                    indent = " " * (len(line) - len(line.lstrip()))
                    line = f"{indent}{line.lstrip()[3:]}"
        elif line.lstrip() == "where":
            errors += [(ERR_IWH, line_nr, path)]
        if line.lstrip().startswith(":"):
            errors += [(ERR_CLN, line_nr, path)]
        newlines.append((line_nr, line))
    return errors, newlines

def left_arrow_check(lines, path):
    errors = []
    newlines = []
    for line_nr, line, is_comment, in_string in annotate_strings(annotate_comments(lines)):
        if is_comment or in_string:
            newlines.append((line_nr, line))
            continue
        # Allow "←" to be followed by "%" or "`", but not by "`(" or "``(" (since "`()" and "``()"
        # are used for syntax quotations). Otherwise, insert a space after "←".
        new_line = re.sub(r'←(?:(?=``?\()|(?![%`]))(\S)', r'← \1', line)
        if new_line != line:
            errors += [(ERR_ARR, line_nr, path)]
        newlines.append((line_nr, new_line))
    return errors, newlines

def output_message(path, line_nr, code, msg):
    # We are outputting for github. We duplicate path, line_nr and code,
    # so that they are also visible in the plaintext output.
    print(f"::error file={path},line={line_nr},code={code}::{path}:{line_nr} {code}: {msg}")


def format_errors(errors):
    global new_exceptions
    for errno, line_nr, path in errors:
        if (errno, path.resolve(), None) in exceptions:
            continue
        new_exceptions = True
        if errno == ERR_MOD:
            output_message(path, line_nr, "ERR_MOD", "Module docstring missing, or too late")
        if errno == ERR_IBY:
            output_message(path, line_nr, "ERR_IBY", "Line is an isolated 'by'")
        if errno == ERR_IWH:
            output_message(path, line_nr, "ERR_IWH", "Line is an isolated where")
        if errno == ERR_CLN:
            output_message(path, line_nr, "ERR_CLN", "Put : and := before line breaks, not after")
        if errno == ERR_IND:
            output_message(path, line_nr, "ERR_IND", "If the theorem/def statement requires multiple lines, indent it correctly (4 spaces or 2 for `|`)")
        if errno == ERR_ARR:
            output_message(path, line_nr, "ERR_ARR", "Missing space after '←'.")
        if errno == ERR_NSP:
            output_message(path, line_nr, "ERR_NSP", "Non-terminal simp. Replace with `simp?` and use the suggested output")

def lint(path, fix=False):
    global new_exceptions
    with path.open(encoding="utf-8", newline="") as f:
        # We enumerate the lines so that we can report line numbers in the error messages correctly
        # we will modify lines as we go, so we need to keep track of the original line numbers
        lines = f.readlines()
        enum_lines = enumerate(lines, 1)
        newlines = enum_lines
        for error_check in [four_spaces_in_second_line,
                            isolated_by_dot_semicolon_check,
                            left_arrow_check,
                            nonterminal_simp_check]:
            errs, newlines = error_check(newlines, path)
            format_errors(errs)

        if not import_only_check(newlines, path):
            errs, newlines = regular_check(newlines, path)
            format_errors(errs)
    # if we haven't been asked to fix errors, or there are no errors or no fixes, we're done
    if fix and new_exceptions and enum_lines != newlines:
        path.with_name(path.name + '.bak').write_text("".join(l for _,l in newlines), encoding = "utf8")
        shutil.move(path.with_name(path.name + '.bak'), path)

fix = "--fix" in sys.argv
argv = (arg for arg in sys.argv[1:] if arg != "--fix")

for filename in argv:
    lint(Path(filename), fix=fix)

if new_exceptions:
    exit(1)
