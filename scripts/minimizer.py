#!/usr/bin/env python3

import re
import logging
import shutil
import subprocess
import sys
import tempfile

def minimized_filename(original_file):
    name_parts = original_file.split('.')
    if name_parts[-3] == 'min':
        try:
            version = int(name_parts[-2])
            return '.'.join(name_parts[:-3]) + f'.min.{version + 1}.lean'
        except ValueError:
            return '.'.join(name_parts[:-3]) + f'.min.1.lean'
    elif name_parts[-1] == 'lean':
        return '.'.join(name_parts[:-1]) + f'.min.1.lean'
    else:
        return original_file + '.min.1.lean'

def make_definitive(original_file, current_file):
    new_file = minimized_filename(original_file)
    shutil.copyfile(current_file, new_file)
    return new_file

def delete_lineno(line):
    return re.sub('^[^:]+:[0-9]+:[0-9]+: ', '', line)

def ignore_sorry(lines):
    return [line for line in lines if line != 'warning: declaration uses \'sorry\'']

def substantially_similar(result_1, result_2):
    lines_1 = [delete_lineno(line) for line in result_1.stdout.split('\n')]
    lines_2 = [delete_lineno(line) for line in result_2.stdout.split('\n')]
    return ignore_sorry(lines_1) == ignore_sorry(lines_2)

def compile_file(filename):
    logging.debug(f"compile_file: {filename}")
    result = subprocess.run(
        ['lake', 'env', 'lean', filename],
        check=False, # We are expecting an error!
        capture_output=True,
        encoding='utf-8')
    #if result.stdout:
    #    logging.debug("compile_file: stdout =")
    #    logging.debug(result.stdout)
    if result.stderr:
        logging.info("compile_file: stderr =")
        logging.info(result.stderr)
    return result

def try_compile(expected_out, new_file):
    new_out = compile_file(new_file)
    return substantially_similar(expected_out, new_out)

def imports_in(source):
    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        yield match.group(1)

def normalize_lean_code(source):
    """Do some minor transformations to fix easy errors, like duplicated or misplaced import statements."""

    # Organize imports.
    imports = sorted(set(imports_in(source)))
    import_statements = '\n'.join('import ' + import_name for import_name in imports)
    source = import_statements + '\n\n' + re.sub(r'^import (.*)$', '', source, flags=re.MULTILINE)

    # Delete empty lines
    source = re.sub(r'\n\n(\n)+', r'\n\n', source)

    return source

def apply_changes(changes, filename):
    with open(filename, 'r') as file:
        source = file.read()
    # Work backwards, otherwise we'll overwrite later changes.
    last_start = len(source)
    for start, end, replacement in sorted(changes, reverse=True):
        if start > end:
            logging.error(f"apply_changes: start should be less than end: ({start}, {end}, {replacement})")
        elif end > last_start:
            logging.warn(f"apply_changes: skipping change because it overlaps with previous ({last_start}): ({start}, {end}, {replacement})")
        else:
            # logging.debug(f"apply_changes: (source[{start}:{end}] = {source[start:end]} -> {replacement})")
            source = source[:start] + replacement + source[end:]
            last_start = start

    source = normalize_lean_code(source)

    with tempfile.NamedTemporaryFile(mode='w', delete=False) as destination:
        logging.debug(f"apply_changes: {filename} -> {destination.name}")
        destination.write(source)
        return destination.name

def import_to_filename(import_name):
    return import_name.replace('.', '/') + '.lean'

def make_decomposable_pass(change_generator):
    """Turn a change generator into a minimization pass.

    A change generator will be called on a source file name and should return an iterable
    of all edits it wants to make, as a tuple (start, end, replacement)
    indicating that the substring source[start:end] should be replaced with the replacement.
    These changes should be independent, but they don't necessarily need to all make progress.

    The resulting minimization pass will use bisection to figure which subset of edits make progress.
    """

    def bisect_changes(expected_out, changes, filename):
        # Turn the change set from an iterable into a sorted list, so we can check for its length
        # and earlier changes apply to the earlier half of the file.
        # Moreover, sorting this list should help with determinism.
        changes = sorted(list(changes))

        if not changes:
            # Nothing to do, so no progress.
            logging.debug(f"bisect_changes: nothing to do here")
            return False, filename

        # Maybe the changes succeed instantly?
        logging.debug(f"bisect_changes: applying {len(changes)} changes")
        new_file = apply_changes(changes, filename)
        if try_compile(expected_out, new_file):
            return True, new_file

        if len(changes) == 1:
            # The change didn't work, give up.
            return False, filename

        changes_top = changes[:len(changes) // 2]
        changes_bot = changes[len(changes) // 2:]

        # Otherwise, maybe there are some changes in the top half of the file that make progress.
        logging.debug(f"bisect_changes: trying to change the top half")
        progress_top, file_top = bisect_changes(expected_out, changes_top, filename)
        if progress_top:
            # Some progress in the top half, so try making progress in the bottom half too.
            logging.debug(f"bisect_changes: top half is done, let's try the bottom too")
            # TODO: here we might end up retrying some changes that were rejected in `changes_top`
            # (but it should only be a logarithmic number of times, since we're doing bisection)
            _, file_top_and_bot = bisect_changes(expected_out, change_generator(file_top), file_top)
            # No matter whether we had progress in the bottom, we had progress in the top.
            return True, file_top_and_bot
        else:
            logging.debug(f"bisect_changes: trying to change the bottom half")
            return bisect_changes(expected_out, changes_bot, filename)

    def decomposable_pass(expected_out, filename):
        return bisect_changes(expected_out, change_generator(filename), filename)

    return decomposable_pass

def strip_comments(filename):
    """Delete all comments from the source."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'\s--.*$',
                             # Require whitespace before, so we don't try to strip `/--` for example. Use .*$ to match until rest of the line, since '.' doesn't match newlines.
                             source,
                             flags=re.MULTILINE):
        yield match.start(), match.end(), ''

    # Block comments can be nested, so write an actual parser to count the nesting level.
    comment_level = 0
    comment_start = -1
    for start in range(len(source)):
        if source[start:start + len('/-')] == '/-':
            if comment_level == 0:
                comment_start = start
            comment_level += 1
        if source[start:start + len('-/')] == '-/':
            comment_end = start + len('-/')
            comment_level -= 1
            if comment_level < 0:
                # Syntax error? Give up trying to parse this comment.
                comment_level = 0
            elif comment_level == 0:
                # End of the outermost comment.
                yield comment_start, comment_end, ''

def delete_align(filename):
    """Delete all #align commands from the source."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'#align .*$', source, flags=re.MULTILINE): # By default, '.' does not include newlines.
        yield match.start(), match.end(), ''
    for match in re.finditer(r'#align_import .*$', source, flags=re.MULTILINE): # By default, '.' does not include newlines.
        yield match.start(), match.end(), ''

def make_sorry(filename):
    """Replace ':= ...\n\n' with ':= sorry\n\n'"""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r':=.*?\n\n', source, flags=re.DOTALL):
        if match == ':= sorry\n\n': continue # Skip useless changes.
        yield match.start(), match.end(), ':= sorry\n\n'

def delete_imports(filename):
    """Delete an import statement outright. Compare `replace_imports`."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        yield match.start(), match.end(), ''

def replace_imports(filename):
    """Replace an import statement with all the code in the file it imports. Compare `delete_imports`."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        import_name = match.group(1)
        import_filename = import_to_filename(import_name)
        logging.debug(f"replace_imports: import {import_name} -> <include {import_filename}>")
        with open(import_filename, 'r') as imported_file:
            import_source = imported_file.read()
        yield match.start(), match.end(), '\n\nsection\n\n' + import_source + '\n\nend\n\n'

def delete_defs(filename):
    """Erase whole blocks of code delimited by two newlines.."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'\n\n.*?\n\n', source, flags=re.DOTALL):
        yield match.start(), match.end(), '\n\n'

def delete_lines(filename):
    """Erase whole lines."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^.*$', source, flags=re.MULTILINE):
        yield match.start(), match.end(), ''

# Dictionary mapping pass-name to pass-code.
# Add more minimization passes here.
# The order matters: generally, you want the fast-to-finish passes to be on the top.
passes = {
    'strip_comments': make_decomposable_pass(strip_comments),
    'delete_align': make_decomposable_pass(delete_align),
    'delete_defs': make_decomposable_pass(delete_defs),
    'make_sorry': make_decomposable_pass(make_sorry),
#    'delete_lines': make_decomposable_pass(delete_lines),
    'delete_imports': make_decomposable_pass(delete_imports),
    'replace_imports': make_decomposable_pass(replace_imports),
}

def minimize_file(original_file):
    expected_out = compile_file(original_file)

    current_file = original_file
    progress = True
    while progress:
        progress = False

        for pass_name, minimize_pass in passes.items():
            logging.debug(f"minimize_file: running {pass_name} on {current_file}")
            try:
                pass_progress, new_file = minimize_pass(expected_out, current_file)
                if pass_progress:
                    logging.info(f"minimize_file: success: {pass_name} modified {current_file} -> {new_file}")
                    progress = True
                    # Commit to this intermediate result.
                    make_definitive(original_file, new_file)
            except Exception as e:
                logging.error(f"minimize_file: exception in {pass_name}: {e}")

    logging.debug(f"minimize_file: no more passes apply to {current_file}")
    return make_definitive(original_file, current_file)

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    if len(sys.argv) < 2:
        print(f"usage: {sys.argv[0]} <testcase.lean>")
    else:
        original_file = sys.argv[1]
        logging.debug(f"minimize_file: output file will be {minimized_filename(original_file)}")
        min_file = minimize_file(original_file)
        print(min_file)
