/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Complex arctangent

This file defines the complex arctangent `Complex.arctan` as
$$\arctan z = -\frac i2 \log \frac{1 + zi}{1 - zi}$$
and shows that it extends `Real.arctan` to the complex plane. Its Taylor series expansion
$$\arctan z = \frac{(-1)^n}{2n + 1} z^{2n + 1},\ |z|<1$$
is proved in `Complex.hasSum_arctan`.
-/


namespace Complex

open scoped Real

/-- The complex arctangent, defined via the complex logarithm. -/
noncomputable def arctan (z : ℂ) : ℂ := -I / 2 * log ((1 + z * I) / (1 - z * I))

theorem tan_arctan {z : ℂ} (h₁ : z ≠ I) (h₂ : z ≠ -I) : tan (arctan z) = z := by
  unfold tan sin cos
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ two_ne_zero, ← div_mul_eq_mul_div,
    -- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I)), sub_mul, add_mul,
    ← exp_add, neg_mul, neg_add_cancel, exp_zero, ← exp_add, ← two_mul]
  have z₁ : 1 + z * I ≠ 0 := by
    contrapose! h₁
    rw [add_eq_zero_iff_neg_eq, ← div_eq_iff I_ne_zero, div_I, neg_one_mul, neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I ≠ 0 := by
    contrapose! h₂
    rw [sub_eq_zero, ← div_eq_iff I_ne_zero, div_I, one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan, ← mul_rotate, ← mul_assoc,
      show 2 * (I * (-I / 2)) = 1 by field_simp, one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key, ← mul_div_mul_right _ _ z₂, sub_mul, add_mul, div_mul_cancel₀ _ z₂, one_mul,
    show _ / _ * I = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]

/-- `cos z` is nonzero when the bounds in `arctan_tan` are met (`z` lies in the vertical strip
`-π / 2 < z.re < π / 2` and `z ≠ π / 2`). -/
lemma cos_ne_zero_of_arctan_bounds {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re)
    (h₂ : z.re ≤ π / 2) : cos z ≠ 0 := by
  refine cos_ne_zero_iff.mpr (fun k ↦ ?_)
  rw [ne_eq, Complex.ext_iff, not_and_or] at h₀ ⊢
  norm_cast at h₀ ⊢
  rcases h₀ with nr | ni
  · left; contrapose! nr
    rw [nr, mul_div_assoc, neg_eq_neg_one_mul, mul_lt_mul_iff_of_pos_right (by positivity)] at h₁
    rw [nr, ← one_mul (π / 2), mul_div_assoc, mul_le_mul_iff_of_pos_right (by positivity)] at h₂
    norm_cast at h₁ h₂
    change -1 < _ at h₁
    rwa [show 2 * k + 1 = 1 by omega, Int.cast_one, one_mul] at nr
  · exact Or.inr ni

theorem arctan_tan {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re ≤ π / 2) :
    arctan (tan z) = z := by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h, add_mul, sub_mul, one_mul, ← mul_rotate, mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg, ← neg_mul, ← sin_neg, ← cos_neg]
  rw [← exp_mul_I, ← exp_mul_I, ← exp_sub, show z * I - -z * I = 2 * (I * z) by ring, log_exp,
    show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]
  all_goals norm_num
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]

@[simp, norm_cast]
theorem ofReal_arctan (x : ℝ) : (Real.arctan x : ℂ) = arctan x := by
  conv_rhs => rw [← Real.tan_arctan x]
  rw [ofReal_tan, arctan_tan]
  all_goals norm_cast
  · rw [← ne_eq]; exact (Real.arctan_lt_pi_div_two _).ne
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

/-- The argument of `1 + z` for `z` in the open unit disc is always in `(-π / 2, π / 2)`. -/
lemma arg_one_add_mem_Ioo {z : ℂ} (hz : ‖z‖ < 1) : (1 + z).arg ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.mem_Ioo, ← abs_lt, abs_arg_lt_pi_div_two_iff, add_re, one_re, ← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

/-- We can combine the logs in `log (1 + z * I) + -log (1 - z * I)` into one.
This is only used in `hasSum_arctan`. -/
lemma hasSum_arctan_aux {z : ℂ} (hz : ‖z‖ < 1) :
    log (1 + z * I) + -log (1 - z * I) = log ((1 + z * I) / (1 - z * I)) := by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ z₂.1, ← (log_mul_eq_add_log_iff z₁.2 (inv_eq_zero.ne.mpr z₂.2)).mpr,
    div_eq_mul_inv]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv, z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg, sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

/-- The power series expansion of `Complex.arctan`, valid on the open unit disc. -/
theorem hasSum_arctan {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan z) := by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Odd.neg_one_pow (n := 2 * k + 0 + 1) (by simp),
    neg_add_cancel, zero_mul, zero_div, mul_zero, zero_add,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Even.neg_one_pow (n := 2 * (k + 1)) (by simp),
    ← mul_div_assoc (_ / _), ← mul_assoc, show -I / 2 * (1 + 1) = -I by ring]
  congr 1
  rw [mul_pow, pow_succ' I, pow_mul, I_sq,
    show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring, I_mul_I, neg_neg, one_mul]

end Complex

/-- The power series expansion of `Real.arctan`, valid on `-1 < x < 1`. -/
theorem Real.hasSum_arctan {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan x) :=
  mod_cast Complex.hasSum_arctan (z := x) (by simpa)
