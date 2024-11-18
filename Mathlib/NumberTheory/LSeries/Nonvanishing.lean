/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.QuadraticNonvanishing

/-!
# The L-function of a Dirichlet character does not vanish on Re(s) ≥ 1

The main result in this file is `DirichletCharacter.Lfunction_ne_zero_of_one_le_re`:
if `χ` is a Dirichlet character and `s.re ≥ 1` and either `χ` is nontrivial or `s ≠ 1`,
then the L-function of `χ` does not vanish at `s`.

As a consequence, we have the corresponding statement for the Riemann ζ function:
`riemannZeta_ne_zero_of_one_le_re`.

These results are prerequisites for the **Prime Number Theorem** and
**Dirichlet's Theorem** on primes in arithmetic progressions.
-/

section nonvanishing

open Complex

-- This is the key positivity lemma that is used to show that the L-function
-- of a Dirichlet character `χ` does not vanish for `s.re ≥ 1` (unless `χ^2 = 1` and `s = 1`).
private lemma re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [norm_eq_abs, abs_ofReal, _root_.abs_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, Nat.cast_zero, div_zero, mul_zero, one_re, mul_one, add_zero, le_refl]
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_abs_sub_sq_re, ← norm_eq_abs, norm_pow,
      hz]
    convert (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

-- This is the version of the technical positivity lemma for logarithms of Euler factors.
private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have ha₀ : 0 ≤ (n : ℝ) ^ (-x) := Real.rpow_nonneg n.cast_nonneg _
    have ha₁ : (n : ℝ) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
      exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit,
        norm_eq_abs, ← ofReal_natCast, abs_cpow_eq_rpow_re_of_pos (mod_cast by omega)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn', one_mul]
    convert _root_.re_log_comb_nonneg ha₀ ha₁ hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

/-- The logarithms of the Euler factors of a Dirichlet L-series form a summable sequence. -/
lemma summable_neg_log_one_sub_mul_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _) this
    |>.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation in
/-- For positive `x` and nonzero `y` and a Dirichlet character `χ` we have that
`|L(χ^0, x)^3 L(χ, x+iy)^4 L(χ^2, x+2iy)| ≥ 1. -/
lemma norm_LSeries_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀, ← LSeries_eulerProduct_exp_log χ h₁,
    ← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_eq_abs, abs_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_add hsum₀ hsum₁, ← tsum_add (hsum₀.add hsum₁) hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) ↦ χ.re_log_comb_nonneg p.prop.two_le h₀ y

variable [NeZero N]

/-- A variant of `DirichletCharacter.norm_LSeries_product_ge_one` in terms of the L-functions. -/
lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
      LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries 1 h₀,
    χ.LFunction_eq_LSeries h₁, (χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

open Asymptotics Topology Filter

open Homeomorph in
lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunctionTrivChar N (1 + x)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
  have : (fun w : ℂ ↦ LFunctionTrivChar N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunctionTrivChar N (1 + w)) (𝓝[≠] 0)
        (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <| H.isBigO_one ℂ
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

omit [NeZero N] in
private lemma one_add_I_mul_ne_one_or {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    1 + I * y ≠ 1 ∨ χ ≠ 1:= by
  simpa only [ne_eq, add_right_eq_self, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

lemma LFunction_isBigO_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    (fun x : ℝ ↦ LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).continuousAt
  rw [← zero_add (1 + _)] at this
  exact this.comp (f := fun x : ℝ ↦ x + (1 + I * y)) (x := 0) (by fun_prop) |>.tendsto.isBigO_one ℂ

private lemma LFunction_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : LFunction χ (1 + I * y) = 0) :
    (fun x : ℝ ↦ LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

-- intermediate statement, special case of the next theorem
private lemma LFunction_ne_zero_of_not_quadratic_or_ne_one {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    LFunction χ (1 + I * t) ≠ 0 := by
  intro Hz
  have hz₁ : t ≠ 0 ∨ χ ≠ 1 := by
    refine h.symm.imp_right (fun h H ↦ ?_)
    simp only [H, one_pow, ne_eq, not_true_eq_false] at h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 :=
    h.symm.imp_left <| mul_ne_zero two_ne_zero
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by omega), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (χ.norm_LFunction_product_ge_one hx t).le
  have H := (LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3 |>.mul <|
    (χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4 |>.mul <|
    LFunction_isBigO_horizontal _ hz₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_eq_abs, abs_ofReal] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <| H.of_norm_right.trans_isLittleO
    <| isLittleO_id_one.mono nhdsWithin_le_nhds

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish when `s.re = 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem LFunction_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
  · exact h.2 ▸ LFunction_at_one_ne_zero_of_quadratic h.1 <| hχs.neg_resolve_right h.2
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or, ← ne_eq, ← ne_eq, hs', add_right_ne_self] at h
    replace h : χ ^ 2 ≠ 1 ∨ s.im ≠ 0 :=
      h.imp_right (fun H ↦ by exact_mod_cast right_ne_zero_of_mul H)
    exact hs'.symm ▸ χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish for `s.re ≥ 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem LFunction_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  hs.eq_or_lt.casesOn (fun hs ↦ LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs ↦ LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

-- Interesting special case:
variable {χ} in
/-- The L-function of a nontrivial Dirichlet character does not vanish at `s = 1`. -/
theorem LFunction_apply_one_ne_zero (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (.inl hχ) <| one_re ▸ le_rfl

end DirichletCharacter

open DirichletCharacter in
/-- The Riemann Zeta Function does not vanish on the closed half-plane `re s ≥ 1`.
(Note that the value at `s = 1` is a junk value, which happens to be nonzero.) -/
lemma riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₀
  · exact riemannZeta_one_ne_zero
  · exact LFunction_modOne_eq (χ := 1) ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

end nonvanishing
