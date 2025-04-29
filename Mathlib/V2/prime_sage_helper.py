def progress(p):
    return (primitive_root(p), prime_factors(p - 1))

def main(p):
    solved = dict()
    unsolved = set([p])
    while unsolved:
        q = unsolved.pop()
        if q < 100:
            solved[q] = q
            continue
        (a, ps) = progress(q)
        solved[q] = (q, a, ps)
        for p in ps:
            if p not in solved:
                unsolved.add(p)
    return [j for (i, j) in sorted(solved.items())]
