/-
Copyright (c) 2026 Aditya Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Menon
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# IMO 2000 Q2

Let `A`, `B`, `C` be positive reals with `ABC = 1`. Prove that
`(A - 1 + 1 / B)(B - 1 + 1 / C)(C - 1 + 1 / A) ≤ 1`.

## Solution

We follow the first solution from
<https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2>.

We parametrize `A = x / y`, `B = y / z`, `C = z / x` where `x, y, z > 0`.
This reduces the problem to proving `(x - y + z)(y - z + x)(z - x + y) ≤ xyz`.

Writing `u = x - y + z`, `v = y - z + x`, `w = z - x + y`, we have `u + v = 2x`,
`v + w = 2y`, `w + u = 2z`, so any two of `u`, `v`, `w` have a positive sum and hence
at most one of them can be nonpositive. If one is nonpositive the left-hand side is
nonpositive and the inequality is clear. Otherwise all three are positive, and by AM-GM
`uv ≤ ((u + v) / 2) ^ 2 = x ^ 2`, and similarly `vw ≤ y ^ 2` and `wu ≤ z ^ 2`; multiplying
these gives `(uvw) ^ 2 ≤ (xyz) ^ 2`, from which the inequality follows.

## References

* <https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2>

-/

namespace Imo2000Q2

/-- For positive reals `x`, `y`, `z` we have `(x - y + z)(y - z + x)(z - x + y) ≤ xyz`. -/
lemma prod_sub_add_le {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z := by
  -- At most one of the three factors can be nonpositive, since any two of them
  -- sum to twice one of `x`, `y`, `z`. If one is nonpositive, so is the product.
  rcases le_or_gt (x - y + z) 0 with hu | hu
  · have hv : 0 < y - z + x := by linarith
    have hw : 0 < z - x + y := by linarith
    calc (x - y + z) * (y - z + x) * (z - x + y)
        ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
                (mul_nonpos_of_nonpos_of_nonneg hu hv.le) hw.le
      _ ≤ x * y * z := by positivity
  rcases le_or_gt (y - z + x) 0 with hv | hv
  · have hw : 0 < z - x + y := by linarith
    calc (x - y + z) * (y - z + x) * (z - x + y)
        ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
                (mul_nonpos_of_nonneg_of_nonpos hu.le hv) hw.le
      _ ≤ x * y * z := by positivity
  rcases le_or_gt (z - x + y) 0 with hw | hw
  · calc (x - y + z) * (y - z + x) * (z - x + y)
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le hv.le) hw
      _ ≤ x * y * z := by positivity
  -- All three factors are positive. By AM-GM each pairwise product is bounded by a square:
  have h1 : (x - y + z) * (y - z + x) ≤ x ^ 2 := by linarith [sq_nonneg (y - z)]
  have h2 : (y - z + x) * (z - x + y) ≤ y ^ 2 := by linarith [sq_nonneg (z - x)]
  have h3 : (z - x + y) * (x - y + z) ≤ z ^ 2 := by linarith [sq_nonneg (x - y)]
  -- Multiplying the three bounds gives the squared inequality, and both sides are positive.
  refine le_of_sq_le_sq ?_ (by positivity)
  calc ((x - y + z) * (y - z + x) * (z - x + y)) ^ 2
      = ((x - y + z) * (y - z + x)) * ((y - z + x) * (z - x + y))
          * ((z - x + y) * (x - y + z)) := by ring
    _ ≤ x ^ 2 * y ^ 2 * z ^ 2 := by gcongr
    _ = (x * y * z) ^ 2 := by ring

/-- **IMO 2000 Q2**. If `A`, `B`, `C > 0` and `ABC = 1`, then
`(A - 1 + 1 / B)(B - 1 + 1 / C)(C - 1 + 1 / A) ≤ 1`. -/
theorem imo2000_q2 {A B C : ℝ}
    (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C) (h_prod : A * B * C = 1) :
    (A - 1 + 1 / B) * (B - 1 + 1 / C) * (C - 1 + 1 / A) ≤ 1 := by
  obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ :
      ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ A = x / y ∧ B = y / z ∧ C = z / x :=
    ⟨A, 1, 1 / B, by grind only [inv_pos]⟩
  have key : (x / y - 1 + 1 / (y / z)) * (y / z - 1 + 1 / (z / x)) * (z / x - 1 + 1 / (x / y))
      = (x - y + z) * (y - z + x) * (z - x + y) / (x * y * z) := by
    field_simp
  rw [key, div_le_one (by positivity)]
  exact prod_sub_add_le x_pos y_pos z_pos

end Imo2000Q2
