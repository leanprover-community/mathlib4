/-
Copyright (c) 2026 Aditya Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Menon
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# IMO 2000 Q2

**Problem**: Let $A$, $B$, $C$ be positive reals with $ABC = 1$.
Prove that $(A - 1 + 1/B)(B - 1 + 1/C)(C - 1 + 1/A) ≤ 1$.

**Solution**:
We follow the first solution from the [Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php?title=2000_IMO_Problems/Problem_2) website.

We parametrize $A = x/y$, $B = y/z$, $C = z/x$ where $x, y, z > 0$.
This reduces the problem to proving $(x - y + z)(y - z + x)(z - x + y) ≤ 8xyz$.

We then reparametrize $x = q + r$, $y = r + p$, $z = p + q$ where $p, q, r ∈ ℝ$,
which transforms the inequality to $(q + r)(r + p)(p + q) ≥ 8pqr$.

The proof splits into cases based on the signs of $p$, $q$, $r$.
When all are positive, AM-GM gives the result.
When at least one is negative or zero, the inequality is verified by sign analysis.
-/

namespace Imo2000Q2

variable {A B C : ℝ}

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

lemma eight_mul_le_prod_add_of_add_pos {p q r : ℝ} (p_add_q_pos : 0 < p + q)
    (r_add_p_pos : 0 < r + p) (q_add_r_pos : 0 < q + r) :
    r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  rcases (lt_or_ge 0 p) with p_pos | p_nonpos <;>
  rcases (lt_or_ge 0 q) with q_pos | q_nonpos <;>
  rcases (lt_or_ge 0 r) with r_pos | r_nonpos
  -- only one of p, q, r can be negative
  all_goals try linarith
  · exact eight_mul_le_prod_add_of_pos p_pos q_pos r_pos
  · convert eight_mul_le_prod_add_of_nonpos r_nonpos q_pos p_pos r_add_p_pos q_add_r_pos using 1
    all_goals ring
  · convert eight_mul_le_prod_add_of_nonpos q_nonpos p_pos r_pos q_add_r_pos p_add_q_pos using 1
    all_goals ring
  · exact eight_mul_le_prod_add_of_nonpos p_nonpos r_pos q_pos p_add_q_pos r_add_p_pos

theorem imo2000_q2 (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C) (h_prod : A * B * C = 1) :
    (A - 1 + 1/B) * (B - 1 + 1/C) * (C - 1 + 1/A) ≤ 1 := by
  obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ : ∃ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧
    A = x / y ∧ B = y / z ∧ C = z / x := by
    use A, 1, 1/B
    grind only [!inv_pos]
  field_simp
  rw [show x = (z + x - y) / 2 + (x + y - z) / 2 by ring] at x_pos
  rw [show y = (x + y - z) / 2 + (y + z - x) / 2 by ring] at y_pos
  rw [show z = (y + z - x) / 2 + (z + x - y) / 2 by ring] at z_pos
  grind only [eight_mul_le_prod_add_of_add_pos  z_pos y_pos x_pos]

end Imo2000Q2
