#!/usr/bin/env python3
"""Mechanical insertion of algebra instance parameters for normed group unbundling.

For each [NormedClass TypeExpr] instance parameter found in .lean files,
inserts the corresponding [AlgebraClass TypeExpr] immediately before it,
unless the algebra is already provided by another class in scope.

Usage:
    python3 scripts/unbundle_normed_group.py [--dry-run]
"""

import re
import sys
from pathlib import Path

# Mapping from normed class to required algebra class
NORMED_TO_ALGEBRA = {
    'SeminormedAddGroup': 'AddGroup',
    'SeminormedGroup': 'Group',
    'NormedAddGroup': 'AddGroup',
    'NormedGroup': 'Group',
    'SeminormedAddCommGroup': 'AddCommGroup',
    'SeminormedCommGroup': 'CommGroup',
    'NormedAddCommGroup': 'AddCommGroup',
    'NormedCommGroup': 'CommGroup',
}

# Regex matching any normed class name (longest first for correct matching)
NORMED_CLASS_RE = '|'.join(sorted(NORMED_TO_ALGEBRA.keys(), key=len, reverse=True))

# For each required algebra, which existing classes provide it?
# These are classes that still extend their algebra (not unbundled).
ALGEBRA_PROVIDERS = {
    'AddGroup': {
        'AddGroup', 'AddCommGroup', 'AddGroupWithOne',
        'Ring', 'CommRing', 'Field', 'DivisionRing',
        'NonUnitalRing', 'NonUnitalCommRing', 'NonUnitalNonAssocRing',
        'NonUnitalSeminormedRing', 'NonUnitalNormedRing',
        'SeminormedRing', 'NormedRing',
        'SeminormedCommRing', 'NormedCommRing',
        'NormedField', 'NontriviallyNormedField',
        'NormedDivisionRing', 'DenselyNormedField',
        'RCLike', 'IsROrC',
        'LinearOrderedField', 'LinearOrderedRing', 'LinearOrderedCommRing',
        'OrderedRing', 'OrderedCommRing',
        'StrictOrderedRing', 'StrictOrderedCommRing',
        'OrderedAddCommGroup', 'LinearOrderedAddCommGroup',
    },
    'Group': {
        'Group', 'CommGroup',
        'OrderedCommGroup',
    },
    'AddCommGroup': {
        'AddCommGroup',
        'Ring', 'CommRing', 'Field', 'DivisionRing',
        'NonUnitalRing', 'NonUnitalCommRing', 'NonUnitalNonAssocRing',
        'NonUnitalSeminormedRing', 'NonUnitalNormedRing',
        'SeminormedRing', 'NormedRing',
        'SeminormedCommRing', 'NormedCommRing',
        'NormedField', 'NontriviallyNormedField',
        'NormedDivisionRing', 'DenselyNormedField',
        'RCLike', 'IsROrC',
        'LinearOrderedField', 'LinearOrderedRing', 'LinearOrderedCommRing',
        'OrderedRing', 'OrderedCommRing',
        'StrictOrderedRing', 'StrictOrderedCommRing',
        'OrderedAddCommGroup', 'LinearOrderedAddCommGroup',
    },
    'CommGroup': {
        'CommGroup',
        'OrderedCommGroup',
    },
}

# Directories to process
DIRS = ['Mathlib', 'Archive', 'Counterexamples', 'MathlibTest']

# Files to skip (already updated)
SKIP_FILES = {
    'Mathlib/Analysis/Normed/Group/Defs.lean',
}


def compute_comment_mask(text):
    """Compute a mask: 0 = normal code, 1 = in comment or string."""
    n = len(text)
    mask = bytearray(n)
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False

    while i < n:
        if in_line_comment:
            mask[i] = 1
            if text[i] == '\n':
                in_line_comment = False
            i += 1
        elif in_string:
            mask[i] = 1
            if text[i] == '\\' and i + 1 < n:
                mask[i + 1] = 1
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
        elif block_depth > 0:
            mask[i] = 1
            if i + 1 < n:
                two = text[i:i + 2]
                if two == '/-':
                    mask[i + 1] = 1
                    block_depth += 1
                    i += 2
                    continue
                elif two == '-/':
                    mask[i + 1] = 1
                    block_depth -= 1
                    i += 2
                    continue
            i += 1
        else:
            if i + 1 < n:
                two = text[i:i + 2]
                if two == '/-':
                    mask[i] = 1
                    mask[i + 1] = 1
                    block_depth += 1
                    i += 2
                    continue
                elif two == '--':
                    mask[i] = 1
                    mask[i + 1] = 1
                    in_line_comment = True
                    i += 2
                    continue
            if text[i] == '"':
                mask[i] = 1
                in_string = True
                i += 1
                continue
            i += 1

    return mask


def find_matching_bracket(text, start):
    """Find the matching ] for [ at position start. Returns end pos (after ])."""
    if start >= len(text) or text[start] != '[':
        return -1
    depth = 1
    i = start + 1
    while i < len(text) and depth > 0:
        if text[i] == '[':
            depth += 1
        elif text[i] == ']':
            depth -= 1
        i += 1
    return i if depth == 0 else -1


def parse_bracket_content(content):
    """Parse bracket content into (forall_prefix, class_name, type_expr) or None.

    Handles:
    - 'NormedAddCommGroup E'
    - 'inst : NormedAddCommGroup E'
    - '∀ i, NormedAddCommGroup (E i)'
    """
    s = content.strip()

    # Strip optional instance name (identifier : rest), but not if starts with ∀
    if not s.startswith('∀'):
        name_match = re.match(r'\w+\s*:\s*', s)
        if name_match:
            s = s[name_match.end():]

    # Check for forall form: ∀ binders, NormedClass TypeExpr
    forall_match = re.match(
        r'(∀\s+.+?,\s*)(' + NORMED_CLASS_RE + r')\s+(.+)',
        s, re.DOTALL
    )
    if forall_match:
        return (forall_match.group(1), forall_match.group(2),
                forall_match.group(3).strip())

    # Simple form: NormedClass TypeExpr
    simple_match = re.match(r'(' + NORMED_CLASS_RE + r')\s+(.+)', s, re.DOTALL)
    if simple_match:
        return ('', simple_match.group(1), simple_match.group(2).strip())

    return None


def find_declaration_start_line(lines, current_line):
    """Find the line number where the current declaration starts."""
    DECL_KEYWORDS = (
        'variable', 'theorem', 'lemma', 'def ', 'noncomputable',
        'instance', 'class ', 'structure ', 'abbrev ', 'example',
        'private ', 'protected ', '@[',
    )
    for j in range(current_line, -1, -1):
        stripped = lines[j].lstrip()
        if any(stripped.startswith(kw) for kw in DECL_KEYWORDS):
            return j
        # Blank line means new context
        if not stripped:
            return min(j + 1, current_line)
    return 0


def has_provider_in_context(context, required_algebra, type_expr, forall_prefix):
    """Check if context already provides the required algebra for type_expr."""
    providers = ALGEBRA_PROVIDERS.get(required_algebra, set())
    escaped_type = re.escape(type_expr)

    for provider in providers:
        escaped_prov = re.escape(provider)
        if forall_prefix:
            # For forall form, check [∀ ..., Provider TypeExpr]
            pat = (r'\[(?:\w+\s*:\s*)?∀\s+.+?,\s*'
                   + escaped_prov + r'\s+' + escaped_type + r'\s*\]')
        else:
            # For simple form, check [Provider TypeExpr]
            pat = (r'\[(?:\w+\s*:\s*)?'
                   + escaped_prov + r'\s+' + escaped_type + r'\s*\]')

        if re.search(pat, context):
            return True

    return False


def process_file(filepath, dry_run=False):
    """Process a single .lean file. Returns number of insertions made."""
    with open(filepath, 'r') as f:
        text = f.read()

    comment_mask = compute_comment_mask(text)
    lines = text.split('\n')

    # Collect all candidate insertions: (position, insertion_text)
    raw_insertions = []

    i = 0
    while i < len(text):
        if text[i] == '[' and not comment_mask[i]:
            end = find_matching_bracket(text, i)
            if end == -1:
                i += 1
                continue

            content = text[i + 1:end - 1]
            parsed = parse_bracket_content(content)

            if parsed is not None:
                forall_prefix, normed_class, type_expr = parsed
                required_algebra = NORMED_TO_ALGEBRA[normed_class]

                # Build context: look back up to 10000 chars
                ctx_start = max(0, i - 10000)
                context = text[ctx_start:i]

                if not has_provider_in_context(
                    context, required_algebra, type_expr, forall_prefix
                ):
                    # Build insertion text
                    if forall_prefix:
                        ins = f'[{forall_prefix}{required_algebra} {type_expr}] '
                    else:
                        ins = f'[{required_algebra} {type_expr}] '
                    raw_insertions.append((i, ins))

            i = end
        else:
            i += 1

    if not raw_insertions:
        return 0

    # Deduplicate: same insertion text in same declaration → keep first only
    deduped = []
    seen = set()
    for pos, insertion in raw_insertions:
        line_num = text[:pos].count('\n')
        decl_start = find_declaration_start_line(lines, line_num)
        key = (decl_start, insertion)
        if key not in seen:
            seen.add(key)
            deduped.append((pos, insertion))

    if dry_run:
        return len(deduped)

    # Apply insertions in reverse order to preserve positions
    result = text
    for pos, insertion in reversed(deduped):
        result = result[:pos] + insertion + result[pos:]

    with open(filepath, 'w') as f:
        f.write(result)

    return len(deduped)


def main():
    dry_run = '--dry-run' in sys.argv

    total = 0
    modified = 0

    for dirname in DIRS:
        root = Path(dirname)
        if not root.exists():
            continue
        for filepath in sorted(root.rglob('*.lean')):
            rel = str(filepath)
            if rel in SKIP_FILES:
                continue

            try:
                n = process_file(filepath, dry_run=dry_run)
                if n > 0:
                    modified += 1
                    total += n
                    print(f"  {rel}: {n} insertion(s)")
            except Exception as e:
                print(f"  ERROR {rel}: {e}", file=sys.stderr)

    action = "would insert" if dry_run else "inserted"
    print(f"\nDone. {action} {total} algebra params in {modified} files.")


if __name__ == '__main__':
    main()
