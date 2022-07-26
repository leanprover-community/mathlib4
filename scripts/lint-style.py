#!/usr/bin/env python3
"""
Lint a file or files from mathlib for style.

Sample usage:

    $ ./scripts/lint-style.py $(find src archive -name '*.lean')

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
exceptions by redirecting the output to ``style-exceptions.txt``:

    $ ./scripts/lint-style.py $(find src archive -name '*.lean') > scripts/style-exceptions.txt
"""

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
ERR_TAC = 9 # imported tactic{,.omega,.observe}
ERR_UNF = 10 # unfreeze_local_instances
WRN_IND = 11 # indentation
WRN_BRC = 12 # curly braces

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
        if errno == "ERR_UNF":
            exceptions += [(ERR_UNF, path)]
        if errno == "WRN_IND":
            exceptions += [(WRN_IND, path)]
        if errno == "WRN_BRC":
            exceptions += [(WRN_BRC, path)]

new_exceptions = False

def skip_comments(enumerate_lines):
    in_comment = False
    for line_nr, line in enumerate_lines:
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

def long_lines_check(lines, path):
    errors = []
    # TODO: some string literals (in e.g. tactic output messages) can be excepted from this rule
    for line_nr, line in enumerate(lines, 1):
        if "http" in line:
            continue
        if len(line) > 101:
            errors += [(ERR_LIN, line_nr, path)]
    return errors

def indent_check(lines, path):
    """Check that tactic blocks are indented correctly.

    This linter warns whenever a `{` symbol starting a subproof appears wrongly indented in a tactic block.
    It does not do much parsing, so to avoid false positives it skips some blocks with complicated syntax
    like nested `begin`/`end` or containing the keywords `calc` or `match`.
    """
    errors = []
    indent_lvl = 0
    in_prf = 0  # counter for nested proof blocks
    check_rest_of_block = True  # we only check uncomplicated syntax
    ended_with_comma = False  # track whether the previous line ends with a comma
    inside_special = 0  # track whether we are inside ⟨⟩ or []
    for line_nr, line in enumerate(lines, 1):
        line = line.split('--')[0] # discard any commented out part of this line
        if len(line) == 0 or line[-1] != '\n':
            line += '\n' # add back newline if it just got removed
        # `lstr` is the line with starting whitespace removed.
        # Therefore, `len(line) - len(lstr)` is the line's indentation depth.
        lstr = line.lstrip(' ')

        # Check that `{` starting a subproof has the expected indentation.
        if in_prf > 0 and check_rest_of_block and ended_with_comma and not inside_special:
            if lstr[0] == '{' and len(line) - len(lstr) != indent_lvl:
                errors += [(WRN_IND, line_nr, path)]

        # Update state for next line.
        ended_with_comma = line.endswith(",\n")
        # We don't want to lint inside `⟨..⟩` (anonymous constructor) or `[..]` tactic blocks.
        inside_special += line.count('⟨') + line.count('[') - line.count('⟩') - line.count(']')
        if line[0] != ' ':
            # This is either the `end` line of a tactic proof, or the first line of a new declaration.
            # Reset the state:
            indent_lvl = 0
            in_prf = 0
            check_rest_of_block = True
            ended_with_comma = False
            inside_special = 0
        if re.match("\b(match|calc)\b", line) is not None:
            check_rest_of_block = False
        if re.match("\bbegin\b", line) is not None:
            # Don't check complicated proof block syntax (note, one if uses `line.find` the other `lstr.find`)
            # in this case, we ignore proof blocks whose outermost-block doesn't begin flush-left
            if line.find("begin") > 0 and in_prf == 0:
                check_rest_of_block = False
            # in this case, we ignore proof blocks where begin is not the first word on the line
            if lstr.find("begin") > 0:
                check_rest_of_block = False
            indent_lvl += 2
            in_prf += 1
        if re.match("\bend\b", line) is not None:
            indent_lvl -= 2
            in_prf -= 1
        indent_lvl += 2 * line.count('{') # potential innocent(?) clash with set-builder notation
        indent_lvl -= 2 * line.count('}') # there can be multiple closing braces on one line
    return errors

def braces_check(lines, path):
    """Check that curly braces are placed correctly.

    This linter warns whenever a `{` (resp. `}`) appears at the end (resp. start) of a line.
    """
    errors = []
    for line_nr, line in enumerate(lines, 1):
        lstr = line.strip()
        if len(lstr) == 0:
            continue
        if lstr[-1] == '{':
            if "goal" in lstr:
                continue
            errors += [(WRN_BRC, line_nr, path)]
        if lstr[0] == '}':
            errors += [(WRN_BRC, line_nr, path)]
    return errors

def import_only_check(lines, path):
    import_only_file = True
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] == "--":
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
        if words[0] != "import" and words[0] != "/-!":
            errors += [(ERR_MOD, line_nr, path)]
            break
        if words[0] == "/-!":
            break
        # final case: words[0] == "import"
        if len(words) > 2:
            if words[2] != "--":
                errors += [(ERR_IMP, line_nr, path)]
    return errors

def import_omega_check(lines, path):
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        imports = line.split()
        if imports[0] != "import":
            break
        if imports[1] in ["tactic", "tactic.omega", "tactic.observe"]:
            errors += [(ERR_TAC, line_nr, path)]
    return errors

def unfreeze_local_instances_check(lines, path):
    errors = []
    for line_nr, line in skip_comments(enumerate(lines, 1)):
        if "unfreeze_local_instances" in line:
            errors += [(ERR_UNF, line_nr, path)]
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
        # We are outputting for github. It doesn't appear to surface code, so show it in the message too
        print(f"::{msg_type} file={path},line={line_nr},code={code}::{code}: {msg}")

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
            output_message(path, line_nr, "ERR_TAC", "Files in mathlib cannot import the whole tactic folder, nor tactic.omega or tactic.observe")
        if errno == ERR_UNF:
            output_message(path, line_nr, "ERR_UNF", "Use of unfreeze_local_instances is discouraged and leads to performance problems, use unfreezingI instead")
        if errno == WRN_IND:
            output_message(path, line_nr, "WRN_IND", "Probable indentation mistake in proof")
        if errno == WRN_BRC:
            output_message(path, line_nr, "WRN_BRC", "Probable misformatting of curly braces")

def lint(path):
    with path.open(encoding="utf-8") as f:
        lines = f.readlines()
        errs = long_lines_check(lines, path)
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
        errs = import_omega_check(lines, path)
        format_errors(errs)
        errs = indent_check(lines, path)
        format_errors(errs)
        errs = braces_check(lines, path)
        format_errors(errs)
        errs = unfreeze_local_instances_check(lines, path)
        format_errors(errs)

for filename in sys.argv[1:]:
    lint(Path(filename))

# if "exceptions" is empty,
# we're trying to generate style-exceptions.txt,
# so new exceptions are expected
if new_exceptions and len(exceptions) > 0:
    exit(1)
