/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Choose.Cast

/-!
# Pochhammer polynomials

This file proves analysis theorems for Pochhammer polynomials.

## Main definitions

* `Differentiable.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is differentiable.

* `ConvexOn.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is convex on `[n-1, ∞)`.

* `descPochhammer_eval_le_sum_descFactorial` is a special case of **Jensen's inequality**
  for `Nat.descFactorial`.

* `descPochhammer_eval_div_factorial_le_sum_choose` is a special case of **Jensen's inequality**
  for `Nat.choose`.
-/


section DescPochhammer

variable {n : ℕ} {𝕜 : Type*} {k : 𝕜} [NontriviallyNormedField 𝕜]

/-- `descPochhammer 𝕜 n` is differentiable. -/
theorem differentiable_descPochhammer_eval : Differentiable 𝕜 (descPochhammer 𝕜 n).eval := by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.finset_prod]

/-- `descPochhammer 𝕜 n` is continuous. -/
theorem continuous_descPochhammer_eval : Continuous (descPochhammer 𝕜 n).eval := by
  exact differentiable_descPochhammer_eval.continuous

lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase (n : ℕ) (k : 𝕜) :
    deriv (descPochhammer 𝕜 n).eval k
      = ∑ i ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase i, (k - j) := by
  simp [descPochhammer_eval_eq_prod_range, deriv_finset_prod]

/-- `deriv (descPochhammer ℝ n)` is monotone on `(n-1, ∞)`. -/
lemma monotoneOn_deriv_descPochhammer_eval (n : ℕ) :
    MonotoneOn (deriv (descPochhammer ℝ n).eval) (Set.Ioi (n - 1 : ℝ)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ioi, Nat.cast_add_one, add_sub_cancel_right] at ha hb
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    apply Finset.sum_le_sum; intro i hi
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      apply sub_nonneg_of_le
      exact ha.le.trans' (mod_cast Nat.le_pred_of_lt hj.2)
    · intro j hj
      rwa [← sub_le_sub_iff_right (j : ℝ)] at hab

/-- `descPochhammer ℝ n` is convex on `[n-1, ∞)`. -/
theorem convexOn_descPochhammer_eval (n : ℕ) :
    ConvexOn ℝ (Set.Ici (n - 1 : ℝ)) (descPochhammer ℝ n).eval := by
  rcases n.eq_zero_or_pos with heq | hpos
  · simp [heq, convexOn_const, convex_Ici]
  · apply MonotoneOn.convexOn_of_deriv (convex_Ici (n - 1 : ℝ))
      continuous_descPochhammer_eval.continuousOn
      differentiable_descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact monotoneOn_deriv_descPochhammer_eval n

/-- The function defined to be `0` for `(-∞, n-1)` and `descPochhammer ℝ n` for `[n-1, ∞)` is
convex on the real line. -/
lemma convexOn_ite_descPochhammer_eval (hn : 1 ≤ n) :
    ConvexOn ℝ Set.univ (fun (x : ℝ) ↦ if n - 1 ≤ x then (descPochhammer ℝ n).eval x else 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  by_cases hx : n - 1 ≤ x <;> by_cases hy : n - 1 ≤ y
  · have hcombo : n - 1 ≤ a*x + b*y := (le_min hx hy).trans (Convex.min_le_combo x y ha hb hab)
    simpa [hcombo, hx, hy] using (convexOn_descPochhammer_eval n).2 hx hy ha hb hab
  · have hcombo' : a*x + b*y ≤ a*x + b*(n - 1) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (le_of_not_le hy) hb) (a*x)
    by_cases hcombo : n - 1 ≤ a*x + b*y
    · trans (descPochhammer ℝ n).eval (a*x + b*(n - 1))
      · simpa [hcombo] using monotoneOn_descPochhammer_eval n hcombo (hcombo.trans hcombo') hcombo'
      · simpa [← descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn), Nat.cast_pred hn,
          hx, hy] using (convexOn_descPochhammer_eval n).2 hx (le_refl (n - 1 : ℝ)) ha hb hab
    · simpa [hcombo, hx, hy] using mul_nonneg ha (descPochhammer_nonneg hx)
  · have hcombo' : a*x + b*y ≤ a*(n - 1) + b*y :=
      add_le_add_right (mul_le_mul_of_nonneg_left (le_of_not_le hx) ha) (b*y)
    by_cases hcombo : n - 1 ≤ a*x + b*y
    · trans (descPochhammer ℝ n).eval (a*(n - 1) + b*y)
      · simpa [hcombo] using monotoneOn_descPochhammer_eval n hcombo (hcombo.trans hcombo') hcombo'
      · simpa [← descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn), Nat.cast_pred hn,
          hx, hy] using (convexOn_descPochhammer_eval n).2 (le_refl (n - 1 : ℝ)) hy ha hb hab
    · simpa [hcombo, hx, hy] using mul_nonneg hb (descPochhammer_nonneg hy)
  · have hcombo : a*x + b*y ≤ n - 1 :=
      (Convex.combo_le_max x y ha hb hab).trans (max_le (le_of_not_le hx) (le_of_not_le hy))
    rcases lt_or_eq_of_le hcombo with hlt | heq
    · simp [not_le_of_lt hlt, hx, hy]
    · simpa [heq, hx, hy, Nat.cast_pred hn] using
        (descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn)).le

private lemma ite_descPochhammer_eval_eq_descFactorial (k n : ℕ) :
    (if (n - 1 : ℝ) ≤ (k : ℝ) then (descPochhammer ℝ n).eval (k : ℝ) else 0)
      = k.descFactorial n := by
  rw [descPochhammer_eval_eq_descFactorial ℝ k n, ite_eq_left_iff, not_le, eq_comm,
    Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, ← @Nat.cast_lt ℝ]
  exact (sub_lt_self (n : ℝ) zero_lt_one).trans'

/-- Special case of **Jensen's inequality** for `Nat.descFactorial`. -/
theorem descPochhammer_eval_le_sum_descFactorial
    (hn : 1 ≤ n) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n - 1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i)
      ≤ ∑ i ∈ t, w i * (p i).descFactorial n := by
  let f : ℝ → ℝ := fun (x : ℝ) ↦ if n - 1 ≤ x then (descPochhammer ℝ n).eval x else 0
  suffices h_jensen : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) by
    simpa only [smul_eq_mul, f, h_avg, ite_descPochhammer_eval_eq_descFactorial] using h_jensen
  exact ConvexOn.map_sum_le (convexOn_ite_descPochhammer_eval hn) h₀ h₁ (by simp)

/-- Special case of **Jensen's inequality** for `Nat.choose`. -/
theorem descPochhammer_eval_div_factorial_le_sum_choose
    (hn : 1 ≤ n) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n - 1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i) / n.factorial
      ≤ ∑ i ∈ t, w i * (p i).choose n := by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div,
    mul_div, ← Finset.sum_div, descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n.factorial)
  exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg

end DescPochhammer
