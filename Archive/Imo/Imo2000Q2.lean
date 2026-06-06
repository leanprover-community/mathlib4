/-
Copyright (c) 2026 Aditya Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Menon
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# IMO 2000 Q2

Let $A$, $B$, $C$ be positive reals with $ABC = 1$. Prove that
$(A - 1 + 1/B)(B - 1 + 1/C)(C - 1 + 1/A) ≤ 1$.

## Solution

We follow the first solution from
<https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2>.

We parametrize $A = x/y$, $B = y/z$, $C = z/x$ where $x, y, z > 0$.
This reduces the problem to proving $(x - y + z)(y - z + x)(z - x + y) ≤ 8xyz$.

We then reparametrize $x = q + r$, $y = r + p$, $z = p + q$ where $p, q, r ∈ ℝ$,
which transforms the inequality to $(q + r)(r + p)(p + q) ≥ 8pqr$.

The proof splits into cases based on the signs of $p$, $q$, $r$.
When all are positive, AM-GM gives the result.
When at least one is negative or zero, the inequality is verified by sign analysis.

## Implementation notes

- The inequality is reduced via $A = x/y$, $B = y/z$, $C = z/x$, then the substitution
  $x = q+r$, $y = r+p$, $z = p+q$.
- Helper lemmas prove $8pqr ≤ (p+q)(r+p)(q+r)$ by AM-GM when $p,q,r > 0$ and by sign analysis
  otherwise; the main proof closes with `grind`.

## References

* <https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2>

## Tags

IMO, inequality, AM-GM, reparametrization
-/

namespace Imo2000Q2

variable {A B C : ℝ}

/-! ### Reduction to a symmetric inequality in three variables -/

/-- When $p$, $q$, $r > 0$, $8pqr ≤ (p+q)(r+p)(q+r)$, by writing the difference of squares as a sum
of nonnegative squares. -/
lemma eight_mul_le_prod_add_of_pos {p q r : ℝ} (p_pos : 0 < p)
    (q_pos : 0 < q) (r_pos : 0 < r) :
    r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  refine le_of_sq_le_sq ?_ (by positivity)
  apply le_of_sub_nonneg
  calc
    0
    _ ≤ (p * (q - r) ^ 2 + q * (r - p) ^ 2 + r * (p - q) ^ 2)
      * ((p + q) * (r + p) * (q + r) + r * q * p * 8) := by positivity
    _ = ((p + q) * (r + p) * (q + r)) ^ 2 - (r * q * p * 8) ^ 2 := by ring

/-- When $p ≤ 0$ but $q$, $r > 0$ and both pairwise sums are positive, the left side is
nonpositive so the inequality holds. -/
lemma eight_mul_le_prod_add_of_nonpos {p q r : ℝ} (p_nonpos : p ≤ 0) (r_pos : 0 < r) (q_pos : 0 < q)
    (p_add_q_pos : 0 < p + q) (r_add_p_pos : 0 < r + p) :
    r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  calc
    r * q * p * 8
    _ ≤ 0 := by
      refine mul_nonpos_of_nonpos_of_nonneg ?_ (by norm_num)
      refine mul_nonpos_of_nonneg_of_nonpos ?_ p_nonpos
      positivity
    _ ≤ (p + q) * (r + p) * (q + r) := by positivity

/-- When all three pairwise sums $p+q$, $r+p$, $q+r$ are positive, the inequality holds by casing
on the signs of $p$, $q$, $r$. -/
lemma eight_mul_le_prod_add_of_add_pos {p q r : ℝ} (p_add_q_pos : 0 < p + q)
    (r_add_p_pos : 0 < r + p) (q_add_r_pos : 0 < q + r) :
    r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  rcases (lt_or_ge 0 p) with p_pos | p_nonpos <;>
  rcases (lt_or_ge 0 q) with q_pos | q_nonpos <;>
  rcases (lt_or_ge 0 r) with r_pos | r_nonpos
  -- At most one of `p`, `q`, `r` can be negative; otherwise some pairwise sum is nonpositive.
  all_goals try linarith
  · exact eight_mul_le_prod_add_of_pos p_pos q_pos r_pos
  · -- `r` is the unique nonpositive variable.
    convert eight_mul_le_prod_add_of_nonpos r_nonpos q_pos p_pos r_add_p_pos q_add_r_pos using 1
    all_goals ring
  · -- `q` is the unique nonpositive variable.
    convert eight_mul_le_prod_add_of_nonpos q_nonpos p_pos r_pos q_add_r_pos p_add_q_pos using 1
    all_goals ring
  · -- `p` is the unique nonpositive variable.
    exact eight_mul_le_prod_add_of_nonpos p_nonpos r_pos q_pos p_add_q_pos r_add_p_pos

/-! ### Main theorem -/

/-- **IMO 2000 Q2**. If $A$, $B$, $C > 0$ and $ABC = 1$, then
$(A - 1 + 1/B)(B - 1 + 1/C)(C - 1 + 1/A) ≤ 1$. -/
theorem imo2000_q2 (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C) (h_prod : A * B * C = 1) :
    (A - 1 + 1/B) * (B - 1 + 1/C) * (C - 1 + 1/A) ≤ 1 := by
  -- Choose `x`, `y`, `z > 0` with `A = x/y`, `B = y/z`, `C = z/x`; then `ABC = 1` automatically.
  obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ : ∃ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧
    A = x / y ∧ B = y / z ∧ C = z / x := by
    use A, 1, 1/B
    grind only [!inv_pos]
  field_simp
  -- Substitute x = q + r, y = r + p, z = p + q, it suffices to show (q + r)(r + p)(p + q) ≥ 8pqr
  rw [show x = (z + x - y) / 2 + (x + y - z) / 2 by ring] at x_pos
  rw [show y = (x + y - z) / 2 + (y + z - x) / 2 by ring] at y_pos
  rw [show z = (y + z - x) / 2 + (z + x - y) / 2 by ring] at z_pos
  grind only [eight_mul_le_prod_add_of_add_pos z_pos y_pos x_pos]

end Imo2000Q2
