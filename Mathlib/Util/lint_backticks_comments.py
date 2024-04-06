#!/usr/bin/env python3
"""
Lint the contents of all backticks in comments: for old declaration names, old file names
or possibly further things.
"""

if __name__ == '__main__':
    # Import input data:
    # - all align_import statements, looking for filesnames we don't want
    # - all align statements, to parse out old lemma names
    # Read in all align_import statements and parse out the name of the old file.
    old_files = []
    for line in open('/home/michael/align_imports.txt', 'r', encoding='utf-8'):
        if not line.startswith("#align_import "):
            continue
        line = line[len("#align_import "):]
        if not " from " in line:
            continue
        old_file = line[:line.find(' from ')]
        old_files.append(old_file)
    # Read in all #align statements and parse the names of the old and new declaration.
    aligns = dict()
    for line in open('/home/michael/all_aligns.txt', 'r', encoding='utf-8'):
        line = line.strip()
        if not line.startswith("#align "):
            continue
        parts = line.split(' ')
        if len(parts) != 3:
            continue
        _align, old_decl, new_decl = parts
        aligns[old_decl] = new_decl
    # For each old declaration, if the new declaration is different
    # *and* there is no new declaration of the same name, add these to our list.
    # We do this in two stages; a naive algorithm is extremely slow (quadratic?).
    old_declarations = []
    for old, new in aligns.items():
        if old != new: # and old not in aligns.values():
            old_declarations.append(old)
    same = set(aligns.values()).intersection(set(old_declarations))
    print(f"Found {len(same)} old declarations which occur as a different new declaration:\n{same}")
    old_declarations = [s for s in old_declarations if s not in same]
    assert "CommRing" not in old_declarations
    # we had all mathlib lemma names... no, we don't need these.
    # known_decls = []
    # for decl in open('/home/michael/first-10k.txt', 'r', encoding='utf-8'):
    #     known_decls.append(decl.strip())
    # Read the input file: flag any string in backticks which is exactly an old file or declaration.
    # TODO: a substring of the old declaration should also work, e.g. just the lemma name
    for line in open('/home/michael/geo-v2.txt', 'r', encoding='utf-8'):
        line=line.strip()
        s = extract_backticks(line)
        if s is None:
            print(f'what, what input did we get: "{line}"')
            assert False # omit invalid input for now
        for item in s:
            if item in old_files:
                print(f'old file {item} mentioned in line: "{line}"')
            if item in old_declarations:
                print(f'old declaration {item} mentioned in line: "{line}"')
