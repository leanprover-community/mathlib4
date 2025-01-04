/-
Copyright (c) 2024 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Pochhammer polynomials

This modules proves analysis results for the Pochhammer polynomials

## Main definitions

* `ConvexOn.descPochhammer_eval` is the proof that the descending Pochhammer polynomial
  `descPochhammer ℝ n` is convex on `[n-1, ∞)`.

* `descPochhammer_eval_le_sum_descFactorial` is a special case of **Jensen's inequality**
  for `Nat.descFactorial`.

* `descPochhammer_eval_div_factorial_le_sum_choose` is a special case of **Jensen's inequality**
  for `Nat.choose`.
-/


section DescPochhammer

variable {n : ℕ} {𝕜 : Type*} {k : 𝕜} [NontriviallyNormedField 𝕜]

lemma descPochhammer_eval_eq_prod_range (n : ℕ) (k : 𝕜) :
    (descPochhammer 𝕜 n).eval k = ∏ j ∈ Finset.range n, (k-j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [descPochhammer_succ_right, ih, ←Finset.prod_range_succ]

/-- `descPochhammer 𝕜 n` is differentiable. -/
theorem Differentiable.descPochhammer_eval : Differentiable 𝕜 (descPochhammer 𝕜 n).eval := by
  simp [descPochhammer_eval_eq_prod_range, Differentiable.finset_prod]

/-- `descPochhammer 𝕜 n` is continuous. -/
theorem Continuous.descPochhammer_eval : Continuous (descPochhammer 𝕜 n).eval := by
  exact Differentiable.descPochhammer_eval.continuous

lemma deriv_descPochhammer_eval_eq_sum_prod_range_erase (n : ℕ) (k : 𝕜) :
    deriv (descPochhammer 𝕜 n).eval k
      = ∑ i ∈ Finset.range n, ∏ j ∈ (Finset.range n).erase i, (k-j) := by
  simp [descPochhammer_eval_eq_prod_range, deriv_finset_prod]

/-- `deriv (descPochhammer ℝ n)` is monotone on `(n-1, ∞)`. -/
lemma MonotoneOn.deriv_descPochhammer_eval (n : ℕ) :
    MonotoneOn (deriv (descPochhammer ℝ n).eval) (Set.Ioi (n-1 : ℝ)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    simp_rw [deriv_descPochhammer_eval_eq_sum_prod_range_erase]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      apply sub_nonneg_of_le
      trans (n : ℝ)
      · rw [Nat.cast_le]
        exact Nat.le_pred_of_lt hj.2
      · rw [Set.mem_Ioi, Nat.cast_add_one, add_sub_cancel_right] at ha
        exact le_of_lt ha
    · intro j hj
      rw [sub_le_sub_iff_right]
      exact hab

/-- `descPochhammer ℝ n` is convex on `[n-1, ∞)`. -/
theorem ConvexOn.descPochhammer_eval (n : ℕ) :
    ConvexOn ℝ (Set.Ici (n-1 : ℝ)) (descPochhammer ℝ n).eval := by
  cases Nat.eq_zero_or_pos n with
  | inl hk =>
    simp [hk, convexOn_const, convex_Ici]
  | inr hk =>
    apply MonotoneOn.convexOn_of_deriv (convex_Ici (n-1 : ℝ))
      Continuous.descPochhammer_eval.continuousOn
      Differentiable.descPochhammer_eval.differentiableOn
    rw [interior_Ici]
    exact MonotoneOn.deriv_descPochhammer_eval n

/-- `0` for `(-∞, n-1)` and `descPochhammer ℝ n` for `[n-1, ∞)` is convex on the real line. -/
lemma ConvexOn.ite_descPochhammer_eval (hn : 1 ≤ n) :
    ConvexOn ℝ Set.univ (fun (x : ℝ) ↦ if n-1 ≤ x then (descPochhammer ℝ n).eval x else 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  by_cases hx : n-1 ≤ x <;> by_cases hy : n-1 ≤ y
  all_goals simp only [hx, hy, ↓reduceIte, smul_eq_mul, mul_zero, add_zero, zero_add]
  · have hcombo : n-1 ≤ a*x+b*y :=
      (le_min hx hy).trans (Convex.min_le_combo x y ha hb hab)
    simp only [hcombo, ↓reduceIte]
    exact (ConvexOn.descPochhammer_eval n).2 hx hy ha hb hab
  · push_neg at hy
    have hcombo' : a*x+b*y ≤ a*x+b*(n-1) := by
      apply add_le_add_left _ (a*x)
      exact mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    by_cases hcombo : n-1 ≤ a*x+b*y
    all_goals simp only [hcombo, ↓reduceIte]
    · trans (descPochhammer ℝ n).eval (a*x+b*(n-1))
      · exact MonotoneOn.descPochhammer_eval n hcombo (hcombo.trans hcombo') hcombo'
      · conv_rhs =>
          rw [←add_zero (a*_), ←mul_zero b,
            ←descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn), Nat.cast_pred hn]
        exact (ConvexOn.descPochhammer_eval n).2 hx (le_refl (n-1 : ℝ)) ha hb hab
    · exact mul_nonneg ha (descPochhammer_nonneg hx)
  · push_neg at hx
    have hcombo' : a*x+b*y ≤ a*(n-1)+b*y := by
      apply add_le_add_right _ (b*y)
      exact  mul_le_mul_of_nonneg_left (le_of_lt hx) ha
    by_cases hcombo : n-1 ≤ a*x+b*y
    all_goals simp only [hcombo, ↓reduceIte]
    · trans (descPochhammer ℝ n).eval (a*(n-1)+b*y)
      · exact MonotoneOn.descPochhammer_eval n hcombo (hcombo.trans hcombo') hcombo'
      · conv_rhs =>
          rw [←zero_add (b*_), ←mul_zero a,
            ←descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn), Nat.cast_pred hn]
        exact (ConvexOn.descPochhammer_eval n).2 (le_refl (n-1 : ℝ)) hy ha hb hab
    · exact mul_nonneg hb (descPochhammer_nonneg hy)
  · push_neg at hx hy
    have hcombo : a*x+b*y ≤ n-1 :=
      (Convex.combo_le_max x y ha hb hab).trans (max_le (le_of_lt hx) (le_of_lt hy))
    cases lt_or_eq_of_le hcombo with
    | inl hcombo =>
      rw [←not_le] at hcombo
      simp [hcombo, ↓reduceIte]
    | inr hcombo =>
      simp [hcombo, ↓reduceIte, ←Nat.cast_pred hn,
        descPochhammer_eval_coe_nat_of_lt (Nat.sub_one_lt_of_lt hn)]

private lemma ite_descPochhammer_eval_eq_descFactorial (k n : ℕ) :
    (if (n-1 : ℝ) ≤ (k : ℝ) then (descPochhammer ℝ n).eval (k : ℝ) else 0)
      = k.descFactorial n := by
  rw [descPochhammer_eval_eq_descFactorial ℝ k n, ite_eq_left_iff, not_le, eq_comm,
    Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, ←Nat.cast_lt (α := ℝ)]
  intro; linarith

/-- Special case of **Jensen's inequality** for `Nat.descFactorial`. -/
theorem descPochhammer_eval_le_sum_descFactorial
    (hn : 1 ≤ n) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n-1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i)
      ≤ ∑ i ∈ t, w i * (p i).descFactorial n := by
  let f : ℝ → ℝ := fun (x : ℝ) ↦ if n-1 ≤ x then (descPochhammer ℝ n).eval x else 0
  suffices h_jensen : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) by
    simpa only [smul_eq_mul, f, h_avg, ↓reduceIte,
      ite_descPochhammer_eval_eq_descFactorial] using h_jensen
  exact ConvexOn.map_sum_le (ConvexOn.ite_descPochhammer_eval hn) h₀ h₁ (by simp)

/-- Special case of **Jensen's inequality** for `Nat.choose`. -/
theorem descPochhammer_eval_div_factorial_le_sum_choose
    (hn : 1 ≤ n) {ι : Type*} {t : Finset ι} (p : ι → ℕ) (w : ι → ℝ)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (h_avg : n-1 ≤ ∑ i ∈ t, w i * p i) :
    (descPochhammer ℝ n).eval (∑ i ∈ t, w i * p i) / n.factorial
      ≤ ∑ i ∈ t, w i * (p i).choose n := by
  simp_rw [Nat.cast_choose_eq_descPochhammer_div, mul_div, ←Finset.sum_div,
    descPochhammer_eval_eq_descFactorial]
  apply div_le_div_of_nonneg_right
  · exact descPochhammer_eval_le_sum_descFactorial hn p w h₀ h₁ h_avg
  · exact Nat.cast_nonneg n.factorial

end DescPochhammer
