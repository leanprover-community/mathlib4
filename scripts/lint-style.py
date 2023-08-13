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
a relative path (like ``src/foo/bar.lean``) will produce errors
that contain the relative path, whilst linting absolute paths (like
``/root/mathlib/src/foo/bar.lean``) will produce errors with the
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

ERR_COP = 0 # copyright header
ERR_IMP = 1 # import statements
ERR_MOD = 2 # module docstring
ERR_LIN = 3 # line length
ERR_SAV = 4 # ᾰ
ERR_RNT = 5 # reserved notation
ERR_OPT = 6 # set_option
ERR_AUT = 7 # malformed authors list
ERR_TAC = 9 # imported Mathlib.Tactic
ERR_UNF = 10 # unfreeze_local_instances
ERR_IBY = 11 # isolated by
ERR_DOT = 12 # isolated or low focusing dot
ERR_SEM = 13 # the substring " ;"
ERR_WIN = 14 # Windows line endings "\r\n"
ERR_TWS = 15 # Trailing whitespace

exceptions = []

SCRIPTS_DIR = Path(__file__).parent.resolve()
ROOT_DIR = SCRIPTS_DIR.parent
RESERVED_NOTATION = ROOT_DIR / 'src/tactic/reserved_notation.lean'


with SCRIPTS_DIR.joinpath("style-exceptions.txt").open(encoding="utf-8") as f:
    for line in f:
        filename, _, _, _, _, errno, *_ = line.split()
        path = ROOT_DIR / filename
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, path)]
        if errno == "ERR_IMP":
            exceptions += [(ERR_IMP, path)]
        if errno == "ERR_MOD":
            exceptions += [(ERR_MOD, path)]
        if errno == "ERR_LIN":
            exceptions += [(ERR_LIN, path)]
        if errno == "ERR_SAV":
            exceptions += [(ERR_SAV, path)]
        if errno == "ERR_RNT":
            exceptions += [(ERR_RNT, path)]
        if errno == "ERR_OPT":
            exceptions += [(ERR_OPT, path)]
        if errno == "ERR_AUT":
            exceptions += [(ERR_AUT, path)]
        if errno == "ERR_TAC":
            exceptions += [(ERR_TAC, path)]

new_exceptions = False

def skip_comments(enumerate_lines):
    in_comment = False
    for line_nr, line in enumerate_lines:
        if line.startswith("--"):
            continue
        if "/-" in line:
            in_comment = True
        if "-/" in line:
            in_comment = False
            continue
        if line == "\n" or in_comment:
            continue
        yield line_nr, line

def skip_string(enumerate_lines):
    in_string = False
    in_comment = False
    for line_nr, line in enumerate_lines:
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
                continue
            if in_string:
                continue
        yield line_nr, line

def small_alpha_vrachy_check(lines, path):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if 'ᾰ' in line:
            errors += [(ERR_SAV, line_nr, path)]
    return errors

def reserved_notation_check(lines, path):
    if path.resolve() == RESERVED_NOTATION:
        return []
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.strip().startswith('reserve') or line.strip().startswith('precedence'):
            errors += [(ERR_RNT, line_nr, path)]
    return errors

def set_option_check(lines, path):
    errors = []
    for line_nr, line in skip_string(skip_comments(enumerate(lines, 1))):
        if line.strip().startswith('set_option'):
            next_two_chars = line.strip().split(' ')[1][:2]
            # forbidden options: pp, profiler, trace
            if next_two_chars == 'pp' or next_two_chars == 'pr' or next_two_chars == 'tr':
                errors += [(ERR_OPT, line_nr, path)]
    return errors

def line_endings_check(lines, path):
    errors = []
    for line_nr, line in enumerate(lines, 1):
        if "\r\n" in line:
            errors += [(ERR_WIN, line_nr, path)]
        line = line.rstrip("\r\n")
        if line.endswith(" "):
            errors += [(ERR_TWS, line_nr, path)]
    return errors

def long_lines_check(lines, path):
    errors = []
    # TODO: some string literals (in e.g. tactic output messages) can be excepted from this rule
    for line_nr, line in enumerate(lines, 1):
        # "!" excludes the porting marker comment
        if "http" in line or "#align" in line or line[0] == '!':
            continue
        if len(line) > 101:
            errors += [(ERR_LIN, line_nr, path)]
    return errors

def import_only_check(lines, path):
    import_only_file = True
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] == "--":
            continue
        if imports[0] == "#align_import":
            continue
        if imports[0] != "import":
            import_only_file = False
            break
        if len(imports) > 2:
            if imports[2] == "--":
                continue
            else:
                errors += [(ERR_IMP, line_nr, path)]
    return (import_only_file, errors)

def regular_check(lines, path):
    errors = []
    copy_started = False
    copy_done = False
    copy_start_line_nr = 0
    copy_lines = ""
    for line_nr, line in enumerate(lines, 1):
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
        if words[0] != "import" and words[0] != "/-!" and words[0] != "#align_import":
            errors += [(ERR_MOD, line_nr, path)]
            break
        if words[0] == "/-!":
            break
        # final case: words[0] == "import"
        if words[0] == "import" and len(words) > 2:
            if words[2] != "--":
                errors += [(ERR_IMP, line_nr, path)]
    return errors

def banned_import_check(lines, path):
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] != "import":
            break
        if imports[1] in ["Mathlib.Tactic"]:
            errors += [(ERR_TAC, line_nr, path)]
    return errors

def isolated_by_dot_semicolon_check(lines, path):
    errors = []
    for line_nr, line in enumerate(lines, 1):
        if line.strip() == "by":
            # We excuse those "by"s following a comma or ", fun ... =>", since generally hanging "by"s
            # should not be used in the second or later arguments of a tuple/anonymous constructor
            # See https://github.com/leanprover-community/mathlib4/pull/3825#discussion_r1186702599
            prev_line = lines[line_nr - 2].rstrip()
            if not prev_line.endswith(",") and not re.search(", fun [^,]* =>$", prev_line):
                errors += [(ERR_IBY, line_nr, path)]
        if line.lstrip().startswith(". ") or line.strip() in (".", "·"):
            errors += [(ERR_DOT, line_nr, path)]
        if " ;" in line:
            errors += [(ERR_SEM, line_nr, path)]
    return errors

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
        print(f"::{msg_type} file={path},line={line_nr},code={code}::{path}#L{line_nr}: {code}: {msg}")

def format_errors(errors):
    global new_exceptions
    for errno, line_nr, path in errors:
        if (errno, path.resolve()) in exceptions:
            continue
        new_exceptions = True
        if errno == ERR_COP:
            output_message(path, line_nr, "ERR_COP", "Malformed or missing copyright header")
        if errno == ERR_IMP:
            output_message(path, line_nr, "ERR_IMP", "More than one file imported per line")
        if errno == ERR_MOD:
            output_message(path, line_nr, "ERR_MOD", "Module docstring missing, or too late")
        if errno == ERR_LIN:
            output_message(path, line_nr, "ERR_LIN", "Line has more than 100 characters")
        if errno == ERR_SAV:
            output_message(path, line_nr, "ERR_SAV", "File contains the character ᾰ")
        if errno == ERR_RNT:
            output_message(path, line_nr, "ERR_RNT", "Reserved notation outside tactic.reserved_notation")
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
            output_message(path, line_nr, "ERR_TWS", "Trailing whitespece detected on line")

def lint(path):
    with path.open(encoding="utf-8", newline="") as f:
        lines = f.readlines()
        errs = line_endings_check(lines, path)
        format_errors(errs)
        lines = [line.rstrip() + "\n" for line in lines]

        errs = long_lines_check(lines, path)
        format_errors(errs)
        errs = isolated_by_dot_semicolon_check(lines, path)
        format_errors(errs)
        (b, errs) = import_only_check(lines, path)
        if b:
            format_errors(errs)
            return # checks below this line are not executed on files that only import other files.
        errs = regular_check(lines, path)
        format_errors(errs)
        errs = small_alpha_vrachy_check(lines, path)
        format_errors(errs)
        errs = reserved_notation_check(lines, path)
        format_errors(errs)
        errs = set_option_check(lines, path)
        format_errors(errs)
        errs = banned_import_check(lines, path)
        format_errors(errs)

for filename in sys.argv[1:]:
    lint(Path(filename))

if new_exceptions:
    exit(1)
