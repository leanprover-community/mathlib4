/-
Copyright (c) 2026 Daniel Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Euler's quadrilateral theorem

This file proves Euler's quadrilateral theorem: for any four points `a`, `b`, `c` and `d`, the sum
of the squares of the four sides of the quadrilateral `a b c d` equals the sum of the squares of
the two diagonals, plus four times the square of the distance between the midpoints of the
diagonals. The theorem is usually stated for a convex quadrilateral, but no hypothesis is needed
here: the quadrilateral may be degenerate and its vertices need not be coplanar.

The correction term is four times a squared distance, so it vanishes exactly when the two
diagonals have the same midpoint. That is the parallelogram hypothesis of
`EuclideanGeometry.dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_of_angle_eq_pi_div_two`. In the
resulting equivalence, the direction that assumes the shared midpoint is the parallelogram law,
stated with distances between points instead of norms of vectors.

## Main results

* `dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq`:
  **Euler's quadrilateral theorem**.
* `dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_iff_midpoint_eq`: the
  parallelogram law, together with its converse.

## References

* https://en.wikipedia.org/wiki/Euler%27s_quadrilateral_theorem

-/

public section

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Euler's quadrilateral theorem**: for any four points, the sum of the squares of the four
sides of the quadrilateral `a b c d` equals the sum of the squares of the two diagonals, plus
four times the square of the distance between the midpoints of the diagonals. -/
theorem dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq
    (a b c d : P) :
    dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2
      = dist a c ^ 2 + dist b d ^ 2 + 4 * dist (midpoint ℝ a c) (midpoint ℝ b d) ^ 2 := by
  have key : ∀ u v w : V, ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2 + ‖u + (v + w)‖ ^ 2
      = ‖u + v‖ ^ 2 + ‖v + w‖ ^ 2 + ‖u + w‖ ^ 2 := by
    intro u v w
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      real_inner_comm u v, real_inner_comm u w, real_inner_comm v w]
    ring
  have hm : (4 : ℝ) * dist (midpoint ℝ a c) (midpoint ℝ b d) ^ 2
      = ‖(a -ᵥ b : V) + (c -ᵥ d)‖ ^ 2 := by
    rw [dist_eq_norm_vsub V, midpoint_vsub_midpoint, midpoint_eq_smul_add, norm_smul,
      invOf_eq_inv, Real.norm_eq_abs]
    ring
  rw [hm, dist_eq_norm_vsub V a b, dist_eq_norm_vsub V b c, dist_eq_norm_vsub V c d,
    dist_eq_norm_vsub V d a, dist_eq_norm_vsub V a c, dist_eq_norm_vsub V b d,
    ← neg_vsub_eq_vsub_rev a d, norm_neg, ← vsub_add_vsub_cancel a b d,
    ← vsub_add_vsub_cancel b c d, ← vsub_add_vsub_cancel a b c]
  exact key _ _ _

/-- The sum of the squares of the four sides of the quadrilateral `a b c d` equals the sum of the
squares of the two diagonals if and only if the two diagonals have the same midpoint. The
direction that assumes the shared midpoint is the parallelogram law, written with distances
between points. -/
theorem dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_iff_midpoint_eq
    (a b c d : P) :
    dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 = dist a c ^ 2 + dist b d ^ 2
      ↔ midpoint ℝ a c = midpoint ℝ b d := by
  rw [dist_sq_add_dist_sq_add_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_add_four_mul_dist_sq,
    add_eq_left, mul_eq_zero_iff_left four_ne_zero, pow_eq_zero_iff two_ne_zero, dist_eq_zero]

end EuclideanGeometry
