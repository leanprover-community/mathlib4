# Basic mathematical properties and objects

This folder is intended to host definitions that are used throughout mathematics without necessarily
belonging to a specific area, such as the notion of a non-empty type or the complex numbers.

Criteria for inclusion in this folder consist of:
1. The concept is used across several mathematical domains.
2. If it is nominally the purview of a particular domain, it is not a primary area of study within
  that domain.
3. The necessary imports are minimal, relative to the inherent complexity of the object.

## Examples

`Nonempty`, `Finite`, `Countable` etc... are used throughout mathematics.
They could arguably be considered concepts in set theory,
but they are not primary objects of study within that discipline.
The necessary imports are minimal, and therefore these are included in the `Basic` folder.

In contrast, `Cardinal`, although used throughout mathematics (e.g., to define `Module.rank`),
is a central object of study within set theory and therefore resides in the `SetTheory` folder.

The real and complex numbers are used throughout mathematics, and, despite the name,
are not only studied in real or complex analysis.
Therefore, the definitions of these belong in the `Basic` folder.

In contrast, while the algebraic structures on `ℝ` or `ℂ` certainly belong in `Basic`,
the analytic structures (`NormedField`, etc.) require comparatively many imports
and consequently belong in the `Analysis` folder.
The order structure on `ℝ` is included in `Basic`, both because the imports remain minimal
and also because it is needed to define `ℝ≥0`.

Generic algebraic structures (groups, rings, fields, etc.) do *not* belong in `Basic`
because these are objects of study for algebraists, despite their ubiquity across
mathematical disciplines. General results about such objects belong in `Algebra`,
whereas more domain-specific ones belong in their respective folders (e.g., `GroupTheory`,
`RingTheory`).

Likewise, generic order-theoretic objects (`PartialOrder`, `Lattice`) are included in
the `Order` folder, because these are still central objects of study within
order theory.

Elementary logic results (e.g. lemmas on propositional logic, or the basic theory of relations)
belong in `Basic`, as the `Logic` folder is reserved for more advanced material (e.g. foundations).
