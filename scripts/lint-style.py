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

This script can also be used to regenerate the list of allowed / ignored style
exceptions by redirecting the output to ``style-exceptions.txt``. Use:

    $ ./scripts/update-style-exceptions.sh

to perform this update.
"""

# TODO: This is adapted from the linter for mathlib3. It should be rewritten in Lean.

from pathlib import Path
import sys
import re
import shutil

ERR_COP = 0 # copyright header
ERR_MOD = 2 # module docstring
ERR_LIN = 3 # line length
ERR_OPT = 6 # set_option
ERR_AUT = 7 # malformed authors list
ERR_TAC = 9 # imported Mathlib.Tactic
ERR_IBY = 11 # isolated by
ERR_DOT = 12 # isolated or low focusing dot
ERR_SEM = 13 # the substring " ;"
ERR_WIN = 14 # Windows line endings "\r\n"
ERR_TWS = 15 # trailing whitespace
ERR_CLN = 16 # line starts with a colon
ERR_IND = 17 # second line not correctly indented
ERR_ARR = 18 # space after "←"
ERR_NUM_LIN = 19 # file is too large
ERR_NSP = 20 # non-terminal simp

exceptions = []

SCRIPTS_DIR = Path(__file__).parent.resolve()
ROOT_DIR = SCRIPTS_DIR.parent


with SCRIPTS_DIR.joinpath("style-exceptions.txt").open(encoding="utf-8") as f:
    for exline in f:
        filename, _, _, _, _, errno, *extra = exline.split()
        path = ROOT_DIR / filename
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, path, None)]
        elif errno == "ERR_MOD":
            exceptions += [(ERR_MOD, path, None)]
        elif errno == "ERR_LIN":
            exceptions += [(ERR_LIN, path, None)]
        elif errno == "ERR_OPT":
            exceptions += [(ERR_OPT, path, None)]
        elif errno == "ERR_AUT":
            exceptions += [(ERR_AUT, path, None)]
        elif errno == "ERR_TAC":
            exceptions += [(ERR_TAC, path, None)]
        elif errno == "ERR_NUM_LIN":
            exceptions += [(ERR_NUM_LIN, path, extra[1])]
        else:
            print(f"Error: unexpected errno in style-exceptions.txt: {errno}")
            sys.exit(1)

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

def set_option_check(lines, path):
    errors = []
    newlines = []
    for line_nr, line, in_comment, in_string in annotate_strings(annotate_comments(lines)):
        if line.strip().startswith('set_option') and not in_comment and not in_string:
            option_prefix = line.strip().split(' ', 2)[1].split('.', 1)[0]
            # forbidden options: pp, profiler, trace
            if option_prefix in {'pp', 'profiler', 'trace'}:
                errors += [(ERR_OPT, line_nr, path)]
                # skip adding this line to newlines so that we suggest removal
                continue
        newlines.append((line_nr, line))
    return errors, newlines

def line_endings_check(lines, path):
    errors = []
    newlines = []
    for line_nr, line in lines:
        if "\r\n" in line:
            errors += [(ERR_WIN, line_nr, path)]
            line = line.replace("\r\n", "\n")
        if line.endswith(" \n"):
            errors += [(ERR_TWS, line_nr, path)]
            line = line.rstrip() + "\n"
        newlines.append((line_nr, line))
    return errors, newlines

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
            if not (next_line == '\n' or next_line.startswith("#") or stripped_next_line.startswith("--") or "rfl" in next_line or "aesop" in next_line):
                num_next_spaces = len(next_line) - len(stripped_next_line)
                # Check if the number of leading spaces is the same
                if num_spaces == num_next_spaces:
                    # If so, the simp is nonterminal
                    errors += [(ERR_NSP, line_nr, path)]
                    new_line = line.replace("simp", "simp?")
        newlines.append((line_nr, new_line))
    newlines.append(lines[-1])
    return errors, newlines

def long_lines_check(lines, path):
    errors = []
    # TODO: find a good way to break long lines
    # TODO: some string literals (in e.g. tactic output messages) can be excepted from this rule
    for line_nr, line in lines:
        if "http" in line or "#align" in line:
            continue
        if len(line) > 101:
            errors += [(ERR_LIN, line_nr, path)]
    return errors, lines

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
    copy_start_line_nr = 1
    copy_lines = ""
    for line_nr, line in lines:
        if not copy_started and line == "\n":
            errors += [(ERR_COP, copy_start_line_nr, path)]
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            copy_start_line_nr = line_nr
            continue
        if not copy_started:
            errors += [(ERR_COP, line_nr, path)]
        if copy_started and not copy_done:
            copy_lines += line
            if "Author" in line:
                # Validating names is not a reasonable thing to do,
                # so we just look for the two common variations:
                # using ' and ' between names, and a '.' at the end of line.
                if ((not line.startswith("Authors: ")) or
                    ("  " in line) or
                    (" and " in line) or
                    (line[-2] == '.')):
                    errors += [(ERR_AUT, line_nr, path)]
            if line == "-/\n":
                if ((not "Copyright" in copy_lines) or
                    (not "Apache" in copy_lines) or
                    (not "Authors: " in copy_lines)):
                    errors += [(ERR_COP, copy_start_line_nr, path)]
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

def banned_import_check(lines, path):
    errors = []
    for line_nr, line, is_comment in annotate_comments(lines):
        if is_comment:
            continue
        imports = line.split()
        if imports[0] != "import":
            break
        if imports[1] in ["Mathlib.Tactic"]:
            errors += [(ERR_TAC, line_nr, path)]
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
        if line.lstrip().startswith(". "):
            errors += [(ERR_DOT, line_nr, path)]
            line = line.replace(". ", "· ", 1)
        if line.strip() in (".", "·"):
            errors += [(ERR_DOT, line_nr, path)]
        if " ;" in line:
            errors += [(ERR_SEM, line_nr, path)]
            line = line.replace(" ;", ";")
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
    if len(exceptions) == 0:
        # we are generating a new exceptions file
        # filename first, then line so that we can call "sort" on the output
        print(f"{path} : line {line_nr} : {code} : {msg}")
    else:
        if code.startswith("ERR"):
            msg_type = "error"
        if code.startswith("WRN"):
            msg_type = "warning"
        # We are outputting for github. We duplicate path, line_nr and code,
        # so that they are also visible in the plaintext output.
        print(f"::{msg_type} file={path},line={line_nr},code={code}::{path}:{line_nr} {code}: {msg}")

def format_errors(errors):
    global new_exceptions
    for errno, line_nr, path in errors:
        if (errno, path.resolve(), None) in exceptions:
            continue
        new_exceptions = True
        if errno == ERR_COP:
            output_message(path, line_nr, "ERR_COP", "Malformed or missing copyright header")
        if errno == ERR_MOD:
            output_message(path, line_nr, "ERR_MOD", "Module docstring missing, or too late")
        if errno == ERR_LIN:
            output_message(path, line_nr, "ERR_LIN", "Line has more than 100 characters")
        if errno == ERR_OPT:
            output_message(path, line_nr, "ERR_OPT", "Forbidden set_option command")
        if errno == ERR_AUT:
            output_message(path, line_nr, "ERR_AUT", "Authors line should look like: 'Authors: Jean Dupont, Иван Иванович Иванов'")
        if errno == ERR_TAC:
            output_message(path, line_nr, "ERR_TAC", "Files in mathlib cannot import the whole tactic folder")
        if errno == ERR_IBY:
            output_message(path, line_nr, "ERR_IBY", "Line is an isolated 'by'")
        if errno == ERR_DOT:
            output_message(path, line_nr, "ERR_DOT", "Line is an isolated focusing dot or uses . instead of ·")
        if errno == ERR_SEM:
            output_message(path, line_nr, "ERR_SEM", "Line contains a space before a semicolon")
        if errno == ERR_WIN:
            output_message(path, line_nr, "ERR_WIN", "Windows line endings (\\r\\n) detected")
        if errno == ERR_TWS:
            output_message(path, line_nr, "ERR_TWS", "Trailing whitespace detected on line")
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
        for error_check in [line_endings_check,
                            four_spaces_in_second_line,
                            long_lines_check,
                            isolated_by_dot_semicolon_check,
                            set_option_check,
                            left_arrow_check,
                            nonterminal_simp_check]:
            errs, newlines = error_check(newlines, path)
            format_errors(errs)

        if not import_only_check(newlines, path):
            # Check for too long files: either longer than 1500 lines, or not covered by an exception.
            # Each exception contains a "watermark". If the file is longer than that, we also complain.
            if len(lines) > 1500:
                ex = [e for e in exceptions if e[1] == path.resolve()]
                if ex:
                    (_ERR_NUM, _path, watermark) = list(ex)[0]
                    assert int(watermark) > 500 # protect against parse error
                    is_too_long = len(lines) > int(watermark)
                else:
                    is_too_long = True
                if is_too_long:
                    new_exceptions = True
                    # add up to 200 lines of slack, so simple PRs don't trigger this right away
                    watermark = len(lines) // 100 * 100 + 200
                    output_message(path, 1, "ERR_NUM_LIN", f"{watermark} file contains {len(lines)} lines, try to split it up")
            errs, newlines = regular_check(newlines, path)
            format_errors(errs)
            errs, newlines = banned_import_check(newlines, path)
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
