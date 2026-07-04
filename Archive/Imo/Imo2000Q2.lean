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
This reduces the problem to proving `(x - y + z)(y - z + x)(z - x + y) ≤ 8xyz`.

We then reparametrize `x = q + r`, `y = r + p`, `z = p + q` where `p, q, r ∈ ℝ`,
which transforms the inequality to `8pqr ≤ (q + r)(r + p)(p + q)`.

The proof splits into cases based on the signs of `p`, `q`, `r`.
When all are positive, AM-GM gives the result.
When at least one is negative or zero, the inequality is verified by sign analysis.

## Implementation notes

- The inequality is reduced via `A = x / y`, `B = y / z`, `C = z / x`, then the substitution
  `x = q + r`, `y = r + p`, `z = p + q`.
- Helper lemmas prove `8pqr ≤ (p + q)(r + p)(q + r)` by AM-GM when `p, q, r > 0` and by sign
  analysis otherwise; the main proof closes with `grind`.

## References

* <https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2>

-/

namespace Imo2000Q2

/-- When `p`, `q`, `r > 0`, `8pqr ≤ (p + q)(r + p)(q + r)`, by writing the difference of squares as
a sum of nonnegative squares. -/
lemma eight_mul_le_prod_add_of_pos {p q r : ℝ} (p_pos : 0 < p)
    (q_pos : 0 < q) (r_pos : 0 < r) :
    8 * p * q * r ≤ (p + q) * (q + r) * (r + p) := by
  suffices 0 ≤ ((p + q) * (q + r) * (r + p)) ^ 2 - (8 * p * q * r) ^ 2 from
    le_of_sq_le_sq (le_of_sub_nonneg this) (by positivity)
  calc 0 ≤ (p * (q - r) ^ 2 + q * (r - p) ^ 2 + r * (p - q) ^ 2)
             * ((p + q) * (q + r) * (r + p) + 8 * p * q * r) := by positivity
       _ = ((p + q) * (q + r) * (r + p)) ^ 2 - (8 * p * q * r) ^ 2 := by ring

/-- When `p ≤ 0` but `q`, `r > 0` and both pairwise sums are positive, the left side is
nonpositive so the inequality holds. -/
lemma eight_mul_le_prod_add_of_nonpos {p q r : ℝ} (p_nonpos : p ≤ 0) (r_pos : 0 < r) (q_pos : 0 < q)
    (p_add_q_pos : 0 < p + q) (r_add_p_pos : 0 < r + p) :
    8 * p * q * r ≤ (p + q) * (r + p) * (q + r) := by
  calc 8 * p * q * r ≤ 0 := by grw [mul_nonpos_of_nonpos_of_nonneg ?_ (by positivity)]
                               grw [mul_nonpos_of_nonpos_of_nonneg (by grind) (by positivity)]
                   _ ≤ (p + q) * (r + p) * (q + r) := by positivity

/-- When all three pairwise sums `p + q`, `r + p`, `q + r` are positive, the inequality holds by
casing on the signs of `p`, `q`, `r`. -/
lemma eight_mul_le_prod_add_of_add_pos (p q r : ℝ)
    (hpq : 0 < p + q := by grind)
    (hqr : 0 < q + r := by grind)
    (hrp : 0 < r + p := by grind) :
    8 * p * q * r ≤ (p + q) * (q + r) * (r + p) := by
  rcases lt_or_ge 0 p with p_pos | p_nonpos <;>
  rcases lt_or_ge 0 q with q_pos | q_nonpos <;>
  rcases lt_or_ge 0 r with r_pos | r_nonpos
  -- At most one of `p`, `q`, `r` can be negative; otherwise some pairwise sum is nonpositive.
  · exact eight_mul_le_prod_add_of_pos p_pos q_pos r_pos
  · -- `r` is the unique nonpositive variable.
    convert eight_mul_le_prod_add_of_nonpos r_nonpos q_pos p_pos hrp hqr using 1 <;> ring
  · -- `q` is the unique nonpositive variable.
    convert eight_mul_le_prod_add_of_nonpos q_nonpos p_pos r_pos hqr hpq using 1 <;> ring
  · linarith
  · -- `p` is the unique nonpositive variable.
    convert eight_mul_le_prod_add_of_nonpos p_nonpos r_pos q_pos hpq hrp using 1; ring
  · linarith
  · linarith
  · linarith

/-- **IMO 2000 Q2**. If `A`, `B`, `C > 0` and `ABC = 1`, then
`(A - 1 + 1 / B)(B - 1 + 1 / C)(C - 1 + 1 / A) ≤ 1`. -/
theorem imo2000_q2 {A B C : ℝ}
    (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C) (h_prod : A * B * C = 1) :
    (A - 1 + 1 / B) * (B - 1 + 1 / C) * (C - 1 + 1 / A) ≤ 1 := by
  obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ :
      ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ A = x / y ∧ B = y / z ∧ C = z / x :=
    ⟨A, 1, 1 / B, by grind only [inv_pos]⟩
  -- If `x = q + r`, `y = r + p`, `z = p + q`, it suffices to show `8pqr ≤ (q + r)(r + p)(p + q)`.
  have := eight_mul_le_prod_add_of_add_pos ((y + z - x) / 2) ((z + x - y) / 2) ((x + y - z) / 2)
  field_simp
  grind

end Imo2000Q2
