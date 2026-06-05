/-
Copyright (c) 2026 Aditya Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Menon
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

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

## Main result

- `imo2000_q2`: The main inequality.

## References

See [IMO2000](https://www.imo-official.org/) for the original problem.
-/


-- a = x/y, b = y/z, c = z/x
-- x = a, y = 1, z = 1/b
-- p = (y + z - x) / 2, q = (z + x - y) / 2, r = (x + y - z) / 2
-- x = q + r, y = r + p, z = p + q
-- A = (q + r) / (r + p), B = (r + p) / (p + q), C = (p + q) / (q + r)
-- p = (y + z - x) / 2 = (1 + 1/b - a) / 2
-- q = (z + x - y) / 2 = (1 + a - 1/b) / 2
-- r = (x + y - z) / 2 = (a + 1/b - 1) / 2


-- p ≤ q
-- (1 + 1/b - a) / 2 ≤ (1 + a - 1/b) / 2
-- 1 ≤ ab
-- q ≤ r
-- (1 + a - 1/b) / 2 ≤ (a + 1/b - 1) / 2
-- b ≤ 1


open Real

lemma idkwhattocallit {p q r : ℝ} (p_add_q_pos : 0 < p + q) (r_add_p_pos : 0 < r + p)
    (r_pos : 0 < r) (q_pos : 0 < q) :
    r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  obtain p_pos | p_nonpos : 0 < p ∨ p ≤ 0 := lt_or_ge 0 p
  · refine le_of_sq_le_sq ?_ (by positivity)
    apply le_of_sub_nonneg
    calc
      0
      _ ≤ (p * (q - r) ^ 2 + q * (r - p) ^ 2 + r * (p - q) ^ 2)
        * ((p + q) * (r + p) * (q + r) + 8 * r * q * p) := by positivity
      _ = ((p + q) * (r + p) * (q + r)) ^ 2 - (r * q * p * 8) ^ 2 := by ring
  · trans 0
    · refine mul_nonpos_of_nonpos_of_nonneg ?_ (Nat.ofNat_nonneg' 8)
      refine mul_nonpos_of_nonneg_of_nonpos ?_ p_nonpos
      positivity
    · positivity

lemma idkwhattocallit2 {p q r : ℝ} (p_add_q_pos : 0 < p + q) (r_add_p_pos : 0 < r + p)
    (q_add_r_pos : 0 < q + r) : r * q * p * 8 ≤ (p + q) * (r + p) * (q + r) := by
  rcases (lt_or_ge 0 p) with p_pos | p_nonpos <;>
  rcases (lt_or_ge 0 q) with q_pos | q_nonpos <;>
  rcases (lt_or_ge 0 r) with r_pos | r_nonpos
  -- only one of p, q, r can be negative
  all_goals try linarith
  · apply idkwhattocallit p_add_q_pos r_add_p_pos r_pos q_pos
  · convert idkwhattocallit r_add_p_pos q_add_r_pos q_pos p_pos using 1
    all_goals ring
  · convert idkwhattocallit q_add_r_pos p_add_q_pos p_pos r_pos using 1
    all_goals ring
  · convert idkwhattocallit p_add_q_pos r_add_p_pos r_pos q_pos using 1

-- #print idkwhattocallit

theorem imo2000_q2.extracted_1_5 {x y z : ℝ} (x_pos : 0 < x) (z_pos : 0 < z)
    (x_lt_y_add_z : x < y + z) (z_lt_x_add_y : z < x + y) :
    (x - y + z) * (y - z + x) * (z - x + y) ≤ x * y * z := by
  have := by
    refine idkwhattocallit (p := x - y + z) (q := y - z + x) (r := z - x + y)
      (by grind) (by grind) (by grind) (by grind)
  apply le_of_mul_le_mul_right (a := 8) (a0 := by positivity)
  convert this using 1
  all_goals ring

theorem imo2000_q2.extracted_1_1 (A B C : ℝ) (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C)
    (A_le_B : A ≤ B) (B_le_C : B ≤ C) (h_prod : A * B * C = 1) :
    (A - 1 + 1 / B) * (B - 1 + 1 / C) * (C - 1 + 1 / A) ≤ 1 := by
  sorry

theorem imo2000_q2 (A B C : ℝ) (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C)
    (h_prod : A * B * C = 1) :
    (A - 1 + 1/B) * (B - 1 + 1/C) * (C - 1 + 1/A) ≤ 1 := by
  wlog h : A ≤ B
  · obtain B_le_C | C_le_A : B ≤ C ∨ C ≤ A := by
      grind only
    · specialize this B C A B_pos C_pos A_pos (by rwa [← mul_rotate]) B_le_C
      simpa [← mul_rotate] using this
    · specialize this C A B C_pos A_pos B_pos (by rwa [mul_rotate]) C_le_A
      simpa [mul_rotate] using this
  wlog h : B ≤ C
  ·

    -- have : C ≤ A := by grind
    sorry
  sorry
  -- if a_le_b : A ≤ B then
  --   if b_le_c : B ≤ C then
  --     exact imo2000_q2.extracted_1_1 A B C A_pos B_pos C_pos a_le_b b_le_c h_prod
  --   else

  --     sorry
  -- else
  --   sorry
  -- wlog h : (1 + A - 1/B) / 2 ≤ (A + 1/B - 1) / 2 -- equivalent to h : B ≤ 1
  -- ·
  --   -- rw [mul_right_comm]
  --   -- apply this
  --   sorry
  -- have := idkwhattocallit
  --   (p := (1 + 1/B - A) / 2)
  --   (q := if (1 + A - 1/B) / 2 ≤ (A + 1/B - 1) / 2 then (1 + A - 1/B) / 2 else (A + 1/B - 1) / 2)
  --   (r := if (1 + A - 1/B) / 2 ≤ (A + 1/B - 1) / 2 then (A + 1/B - 1) / 2 else (1 + A - 1/B) / 2)
  --    (by ) (by grind) (by grind) (by grind)
  --   (by grind) (by ring_nf; positivity) h
  -- let a := A ⊓ B ⊓ C
  -- let b := A ⊔ B ⊔ C
  -- let c := 1 / (a * b)
  -- let x := 1
  -- let y := 1 / a
  -- let z := c
  -- have x_pos : 0 < x := by positivity
  -- have y_pos : 0 < y := by positivity
  -- have z_pos : 0 < z := by positivity


  -- obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ : ∃ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧
  --   A = x / y ∧ B = y / z ∧ C = z / x := by
  --   use A, 1, 1/B
  --   simp only [zero_lt_one, one_div, inv_pos, div_one, div_inv_eq_mul, one_mul, true_and]
  --   grind
  -- apply le_of_mul_le_mul_right (a := x * y * z) (a0 := by positivity)
  -- field_simp
  -- exact imo2000_q2.extracted_1_5 x_pos z_pos sorry sorry
-- have := idkwhattocallit (p := x - y + z) (q := y - z + x) (r := z - x + y) (by grind) (by grind)

theorem imo2000_q2_old (A B C : ℝ) (A_pos : 0 < A) (B_pos : 0 < B) (C_pos : 0 < C)
    (h_prod : A * B * C = 1) :
    (A - 1 + 1/B) * (B - 1 + 1/C) * (C - 1 + 1/A) ≤ 1 := by
  obtain ⟨x, y, z, x_pos, y_pos, z_pos, rfl, rfl, rfl⟩ : ∃ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧
    A = x / y ∧ B = y / z ∧ C = z / x := by
    use A, 1, 1/B
    simp only [zero_lt_one, one_div, inv_pos, div_one, div_inv_eq_mul, one_mul, true_and]
    grind
  apply le_of_mul_le_mul_right (a := x * y * z) (a0 := by positivity)
  simp only [one_div, inv_div, one_mul]
  field_simp
  obtain ⟨p, q, r, rfl, rfl, rfl⟩ : ∃ (p q r : ℝ), x = q + r ∧ y = r + p ∧ z = p + q := by
    use (y + z - x) / 2, (z + x - y) / 2, (x + y - z) / 2
    split_ands <;> ring
  conv_lhs => ring_nf
  rw [mul_comm q r, mul_rotate (q + r), mul_comm (r + p)]
  convert idkwhattocallit2 z_pos y_pos x_pos using 1