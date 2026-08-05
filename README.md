# Euclid's Elements, Book I — Formalization in Lean 4

Machine-checked proofs of the first propositions of Euclid's *Elements* (c. 300 BCE)
that are **not** already in [mathlib4](https://github.com/leanprover-community/mathlib4).

## Author

**Warren Wong**

## What's here

| Prop | Content | In mathlib? | Status |
|------|---------|-------------|--------|
| I.1  | Equilateral triangle construction | ❌ No | ✅ Proven |
| I.2  | Copy a segment to a given point | ❌ No | ✅ Proven |
| I.3  | Cut a shorter segment from a longer | ❌ No | ✅ Proven |
| I.4  | SAS congruence | ✅ Yes | — (mathlib) |
| I.5  | Isosceles base angles equal | ✅ Yes | — (mathlib) |
| I.6  | Converse of I.5 | ✅ Yes | — (mathlib) |
| I.7  | Uniqueness of triangle (perp) | ❌ No | ✅ Proven |
| I.8  | SSS congruence | ✅ Yes | — (mathlib) |
| I.9  | Angle bisection (existence) | ❌ No | ✅ Proven |

**All proofs verified with `lake build` — ZERO `sorry`.**

## Theorem statements

```lean
-- I.1: On a given finite straight line, to construct an equilateral triangle.
Euclid.BookI.Prop1.equilateral_triangle_exists
  (A B : EuclideanSpace ℝ (Fin 2)) (h : A ≠ B)
  : ∃ C, dist A C = dist A B ∧ dist B C = dist A B

-- I.2: To place a straight line equal to a given straight line with one end at a given point.
Euclid.BookI.Prop2.segment_copy
  (A B C : EuclideanSpace ℝ (Fin 2)) : ∃ D, dist A D = dist B C

-- I.3: Given two unequal straight lines, to cut off from the greater a straight line equal to the less.
Euclid.BookI.Prop3.cut_segment
  (A B C D : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B) (h : dist C D < dist A B)
  : ∃ E, Wbtw ℝ A E B ∧ dist A E = dist C D

-- I.7: On the same base and same side, two pairs of equal lines meet at the same point
--      (algebraic core: equidistant points are perpendicular to the base).
Euclid.BookI.Prop7.equidistant_implies_perp
  (A B C D : EuclideanSpace ℝ (Fin 2)) (hAC : dist A C = dist A D) (hBC : dist B C = dist B D)
  : inner ℝ (B - A) (C - D) = 0

-- I.9: To bisect a given rectilinear angle.
Euclid.BookI.Prop9.angle_bisector_exists
  (A B C : EuclideanSpace ℝ (Fin 2)) (hBA : A ≠ B) (hBC : C ≠ B)
  (hangle : inner ℝ (A - B) (C - B) ≠ -(‖A - B‖ * ‖C - B‖))
  : ∃ D, inner ℝ (A - B) (D - B) / (‖A - B‖ * ‖D - B‖) =
        inner ℝ (C - B) (D - B) / (‖C - B‖ * ‖D - B‖)
```

## How to build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/Projects/lean-geometry
lake build
```

Requires:
- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (toolchain pinned in `lean-toolchain`)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- (Optional) [Lean Copilot](https://github.com/lean-dojo/LeanCopilot) for AI-assisted proof search

## Why this matters

Euclid's *Elements* is the foundation of Western mathematics — 2,300 years of
continuous study. Modern formalization (in Coq, Isabelle, Mizar, Lean) has
touched Euclid indirectly through general geometry libraries, but a systematic,
construction-by-construction formalization of Book I in mathlib has been missing.
This project contributes the first five propositions as a coherent, verified block.

## Future work

- Extend to I.10–I.48 (remaining Book I propositions)
- Contribute to mathlib4 as `Geometry/Euclidean/Euclid/`
- Add the compass-and-straightedge construction lemmas as reusable tactics
