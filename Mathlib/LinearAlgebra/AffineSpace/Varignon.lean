/-
Copyright (c) 2026 Daniel Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
# Varignon's theorem

This file proves Varignon's theorem: the midpoints of the sides of a quadrilateral form a
parallelogram. The statement is purely affine, so it holds in any affine space over a ring with
invertible `2`, the quadrilateral `p₁ p₂ p₃ p₄` may be degenerate, and its vertices need not be
coplanar.

Here a quadrilateral is a parallelogram when its two diagonals have the same midpoint, the same
convention the British flag theorem uses for its parallelogram hypothesis. The statement that
each side of the quadrilateral of midpoints is one half of a diagonal of `p₁ p₂ p₃ p₄` is
`midpoint_vsub_midpoint_same_middle`, applied to the four cyclic triples of vertices.

## Main results

* `midpoint_midpoint_midpoint_rotate`: **Varignon's theorem**.

## References

* https://en.wikipedia.org/wiki/Varignon%27s_theorem

-/

public section

variable (R : Type*) {V P : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
  [AddTorsor V P]

/-- **Varignon's theorem**: the midpoints of the sides of the quadrilateral `p₁ p₂ p₃ p₄` form a
parallelogram, in the form that the two diagonals of that quadrilateral of midpoints have the
same midpoint. Each of its sides is one half of a diagonal of `p₁ p₂ p₃ p₄`, see
`midpoint_vsub_midpoint_same_middle`. -/
theorem midpoint_midpoint_midpoint_rotate (p₁ p₂ p₃ p₄ : P) :
    midpoint R (midpoint R p₁ p₂) (midpoint R p₃ p₄) =
      midpoint R (midpoint R p₂ p₃) (midpoint R p₄ p₁) :=
  (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 <| by
    rw [midpoint_vsub_midpoint_same_middle, midpoint_comm p₃ p₄,
      midpoint_vsub_midpoint_same_left]
