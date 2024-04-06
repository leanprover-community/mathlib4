#!/usr/bin/env python3
"""
Lint the contents of all backticks in comments: for old declaration names, old file names
or possibly further things.
"""

if __name__ == '__main__':
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
