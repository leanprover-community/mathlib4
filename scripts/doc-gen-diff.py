#!/usr/bin/env python3
# ./scripts/doc-gen-diff.py commit1 commit2 [files...]
# Run doc-gen twice, on different commits, and compare the HTML output between the two versions.
# If `files` are specified, only build and diff those files.

from difflib import unified_diff
from dataclasses import dataclass
from filecmp import dircmp
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

try:
    from lxml.html.diff import htmldiff
except ImportError:
    print("Could not import `lxml`. Hint: try `pip install lxml`.", file=sys.stderr)
    sys.exit(1)
try:
    from bs4 import BeautifulSoup, NavigableString
except ImportError:
    print("Could not import `beautifulsoup4`. Hint: try `pip install beautifulsoup4`.", file=sys.stderr)
    sys.exit(1)

# Lakefile to use for the docbuild directory, with fields to be filled by `str.format`.
DOCBUILD_LAKEFILE="""
name = "docbuild"
reservoir = false
version = "0.1.0"

[[require]]
name = "doc-gen4"
git = "https://github.com/leanprover/doc-gen4.git"
rev = "{docgen4_rev}"

[[require]]
name = "{dep_name}"
git = "{dep_path}/.git"
rev = "{dep_rev}"
"""

@dataclass
class Lakefile:
    pkg_name: str
    default_targets: list

    @classmethod
    def of_lean_file(cls, file):
        contents = file.read().decode('utf-8')
        # TODO: less ad-hoc parsing!
        if match := re.search(r'\npackage (.*) where\n', contents):
            name = match.group(1)
        else:
            raise ValueError("No `package ... where` declaration in lakefile.lean")
        default_targets = []
        for match in re.finditer(r'\n@\[default_target\][ \t\n]+(lean_lib|lean_exe) (.*) where\n', contents):
            default_targets.append(match.group(2))
        return cls(pkg_name=name, default_targets=default_targets)

    @classmethod
    def of_toml_file(cls, file):
        contents = tomllib.load(file)
        return cls(pkg_name=contents['name'], default_targets=contents['default_targets'])

def read_lakefile(filename, file):
    if filename.endswith('.lean'):
        return Lakefile.of_lean_file(file)
    elif filename.endswith('.toml'):
        return Lakefile.ofTomlFile(file)
    else:
        raise ValueError(f"Unknown lakefile format {filename.split('.')[-1]}")

def canonicalize_filename(file):
    if file.endswith('.lean'):
        path = Path(file)
        if path.is_absolute():
            return path.relative_to(pwd)
        else:
            return path
    elif file.count('.') > 2:
        return Path(file.replace('.', '/') + '.lean')
    else:
        raise ValueError(f"Ambiguous file name {file}: should be a relative path ending with `.lean`")

def filename_to_module(file):
    # Remove the file name extension (which should be `.lean`, and then join the module names with dots.
    return '.'.join(Path(file).parts[:-1] + (Path(file).stem,))

def filename_to_htmldoc(file):
    # Remove the file name extension (which should be `.lean`, and then join the module names with dots.
    return Path(file).with_suffix('.html')

def build_docs(docbuild_path, dep_rev, files):
    """Build docs in `docbuild_path/.lake/build/doc` for the files from commit `dep_rev`.
    Returns the process, which can be awaited on (for running the build in parallel).

    :rtype: subprocess.Popen
    """
    with open(docbuild_path / "lakefile.toml", 'w') as lakefile:
        lakefile.write(DOCBUILD_LAKEFILE.format(
            docgen4_rev=lean_version,
            dep_name=lakefile_data.pkg_name,
            dep_path=pwd,
            dep_rev=dep_rev,
        ))
    env = os.environ
    update_result = subprocess.run(['lake', 'update'], cwd=docbuild_path, check=False) # `lake update` can invoke cache, which might complain about missing files
    if files:
        targets = [filename_to_module(file) + ':docs' for file in files]
    else:
        targets = [target + ':docs' for target in lakefile_data.default_targets]
    return subprocess.Popen(
            ['lake', 'build'] + targets,
            cwd=docbuild_path,
            env={'DOCGEN_SRC': 'file', **env}, # Override DOCGEN_SRC, otherwise it complains the repos are not (necessarily) found on Github.
    )

file_url_pattern = re.compile(r'href="file://[^"]*"')
def clean_html_fast(html):
    """First-order cleaning up a HTML string holding a doc-gen generated page, so it can be easily diffed.

    This is a first pass cleanup that tries to strip out easy differences, so the pages can be verified to be equal without fully parsing all the HTML.
    """
    return file_url_pattern.sub("", html)

def clean_html(html):
    """Clean up a HTML string holding a doc-gen generated page, so it can be easily diffed."""
    soup = BeautifulSoup(html)
    body = soup.body
    # Strip out all links to local files (which are going to encode the compilation directory).
    for tag in body.find_all("a"):
        try:
            if tag['href'].startswith('file:///'):
                del tag['href']
        except KeyError:
            continue
    # Speed up diffing by hiding irrelevant tags.
    for tag in body.find_all("nav"):
        tag.decompose()
    # If the only contents of a `<li>` is a single `<p>`, get rid of that `<p>`
    for tag in body.find_all("li"):
        if len(tag.contents) == 1 and tag.contents[0].name == 'p':
            tag.extend(tag.p.extract().contents)
    return body.prettify()

def diff_html(filename1, filename2):
    with open(filename1, 'r') as file1:
        html1 = file1.read()
    with open(filename2, 'r') as file2:
        html2 = file2.read()
    # Quick and dirty cleaning up the HTML, for a fast exit.
    html1 = clean_html_fast(html1)
    html2 = clean_html_fast(html2)
    if html1 == html2:
        return False
    # Thorough cleaning up.
    body1 = clean_html(html1)
    body2 = clean_html(html2)
    if body1 == body2:
        return False
    # TODO: htmldiff does not catch all the differences yet...
    # diff = htmldiff(body1, body2)
    diff = unified_diff(body1.splitlines(keepends=True), body2.splitlines(keepends=True))
    return diff

def print_unified_diff(filename, diff):
    if not diff:
        print(f"{filename}: identical.")
        return

    print(f"{filename}: differences found:")
    sys.stdout.writelines(diff)

def print_html_diff(filename, diff):
    """Nicely format the output of `lxml.html.diff.htmldiff`"""
    if not diff:
        print(f"{filename}: identical.")
        return

    soup = BeautifulSoup(diff)
    if not (soup.find_all('ins') or soup.find_all('del')):
        print(f"{filename}: cannot find difference")
        return
    else:
        print(soup.find_all('ins') + soup.find_all('del'))

    # Remove all tags that do not contain diff-relevant contents.
    def clean(curr):
        if curr.name == 'ins' or curr.name == 'del':
            pass
        elif isinstance(curr, NavigableString) or not (curr.find_all('ins') or curr.find_all('del')):
            curr.decompose()
        else:
            for child in curr.contents:
                clean(child)
    clean(soup)

    print(f"{filename}: differences found:")
    print(soup.prettify())

def print_recursive_html_diff(doc1, doc2, path, dcmp):
    differences = []
    for name in dcmp.left_only:
        print(f"{path/name}: only in {path1}")
    for name in dcmp.right_only:
        print(f"{path/name}: only in {path2}")
    for name in dcmp.diff_files:
        diff = diff_html(doc1 / path / name, doc2 / path / name)
        if diff:
            differences.append(path / name)
            print_unified_diff(path / name, diff)
    for dir, sub_dcmp in dcmp.subdirs.items():
        differences.extend(print_recursive_html_diff(doc1, doc2, path / dir, sub_dcmp))
    return differences

def diff(doc1, doc2, files):
    if not files:
        # Do a full directory comparison
        differences = print_recursive_html_diff(doc1, doc2, Path('.'), dircmp(doc1, doc2))
        print(f"Found {len(differences)} differences.")
    else:
        for file in files:
            diff = diff_html(doc1 / filename_to_htmldoc(file), doc2 / filename_to_htmldoc(file))
            print_unified_diff(file, diff)

# Argument parsing
if len(sys.argv) < 3:
    print("""usage: ./scripts/doc-gen-diff.py commit1 commit2 [files...]

Run doc-gen twice, on different commits, and compare the HTML output between the two versions.
If `files` are specified, only build and diff those files.""", file=sys.stderr)
    sys.exit(1)

# Configuration
pwd = Path(".").absolute()
_, commit1, commit2, *files = sys.argv
files = [canonicalize_filename(file) for file in files]
for lakefilename in ['lakefile.lean', 'lakefile.toml']:
    try:
        with open(lakefilename, 'rb') as lakefile:
            lakefile_data = read_lakefile(lakefilename, lakefile)
            break
    except FileNotFoundError:
        # Try the other lakefile options.
        continue
else:
    print("""No lakefile.lean or lakefile.toml found in the current directory.

    Hint: this script should be run from the root of the project to diff, for example to run it in Mathlib:
        cd mathlib4
        ./scripts/doc-gen-diff.py ...
    """, file=sys.stderr)
    exit(1)
with open('lean-toolchain', 'r') as toolchain_file:
    lean_toolchain = toolchain_file.read().strip()
lean_version = lean_toolchain.split(':')[1]

docbuild1 = Path(tempfile.mkdtemp())
docbuild2 = Path(tempfile.mkdtemp())

# Run the processes in parallel and wait until both are done.
processes = [build_docs(docbuild1, commit1, files), build_docs(docbuild2, commit2, files)]
for process in processes:
    process.wait()

diff(docbuild1 / ".lake" / "build" / "doc", docbuild2 / ".lake" / "build" / "doc", files)
