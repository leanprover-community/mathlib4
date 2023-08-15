#!/usr/bin/env python3

# Tool to add source headers to ported theory files,
# archived for historical purposes.

from pathlib import Path
import re
import yaml

excepts = {
    'categorytheory.category.rel': 'categorytheory.category.relcat',
    'categorytheory.isomorphism': 'categorytheory.iso',
    'categorytheory.naturalisomorphism': 'categorytheory.natiso',
    'categorytheory.naturaltransformation': 'categorytheory.nattrans',
    'leancore.data.vector': 'data.vector',
    'order.monovary': 'order.monotone.monovary'
    }

def condense(s):
    if s.startswith('Mathlib/'):
        s = s[len('Mathlib/'):]
    if s.endswith('.lean'):
        s = s[:-5]
    s = s.lower()
    s = s.replace('/', '.')
    s = s.replace('_', '')
    if s in excepts:
        s = excepts[s]
    return s

port_status = yaml.load(open("mathlib4-port-status.yaml").read())

# map from condensed names to mathlib4 paths
map = {}
for path in Path('Mathlib').glob('**/*.lean'):
    path = str(path)
    map[condense(path)] = path

count = 0
for key, val in port_status.items():
    if val.startswith('Yes'):
        sha = val.split()[2]
        mathlib3 = key
        mathlib4 = map[condense(key)]

        place = '(\n-/\n\n?import )'
        blob = "\n\n! This file was ported from Lean 3 source module " + mathlib3 + "\n" + \
            "! leanprover-community/mathlib commit " + sha + "\n" + \
            "! Please do not edit these lines, except to modify the commit id\n" + \
            "! if you have ported upstream changes."
        old = open(mathlib4).read()

        if blob[1:] in old:     # match even without leading newline
            print(f'{mathlib4} already has header')
        elif "! leanprover-community/mathlib commit " in old:
            m = re.search("^! leanprover-community/mathlib commit (.*)$", old, flags=re.MULTILINE)
            print(f'file says {m.groups()[0]} but we want {sha}')
            assert(False)
        else:
            new = re.sub(place, blob + '\\1', old, flags=re.MULTILINE)
            open(mathlib4, 'w').write(new)
            count += 1

print(count)
