/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
/-!
# Dirichlet series as Mellin transforms

Here we prove general results of the form "the Mellin transform of a power series in exp (-t) is
a Dirichlet series".
-/

open Filter Topology Asymptotics Real Set MeasureTheory
open Complex

variable {ι : Type*} [Countable ι]

/-- Most basic version of the "Mellin transform = Dirichlet series" argument. -/
lemma hasSum_mellin {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * rexp (-p i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (p i) ^ s.re) :
    HasSum (fun i ↦ Gamma s * a i / p i ^ s) (mellin F s) := by
  simp_rw [mellin, smul_eq_mul, ← setIntegral_congr_fun measurableSet_Ioi
    (fun t ht ↦ congr_arg _ (hF t ht).tsum_eq), ← tsum_mul_left]
  convert hasSum_integral_of_summable_integral_norm
    (F := fun i t ↦ t ^ (s - 1) * (a i * rexp (-p i * t))) (fun i ↦ ?_) ?_ using 2 with i
  · simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc (a _), mul_div_assoc, integral_const_mul]
    rcases hp i with hai | hpi
    · rw [hai, zero_mul, zero_mul]
    have := integral_cpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← ofReal_mul, ← ofReal_neg, ← ofReal_exp, ← neg_mul (p i)] at this
    rw [this, one_div, inv_cpow _ _ (arg_ofReal_of_nonneg hpi.le ▸ pi_pos.ne), div_eq_inv_mul]
  · -- integrability of terms
    rcases hp i with hai | hpi
    · simp [hai]
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc]
    have := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (p i), ← integrableOn_Ioi_comp_mul_left_iff _ _ hpi] at this
    refine (IntegrableOn.congr_fun (this.const_mul (1 / p i ^ (s - 1)))
      (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(rexp _) : ℂ), ← mul_assoc, neg_mul, ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hpi.le ht.le, ← mul_assoc, one_div, inv_mul_cancel₀, one_mul]
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr hpi.ne')
  · -- summability of integrals of norms
    apply Summable.of_norm
    convert h_sum.mul_left (Real.Gamma s.re) using 2 with i
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc, norm_mul (a i), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖a i‖, norm_norm]
    rcases hp i with hai | hpi
    · simp [hai]
    congr 1
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← neg_mul (p i), one_div, inv_rpow hpi.le, ← div_eq_inv_mul] at this
    rw [norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)), ← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

/-- Shortcut version for the commonly arising special case when `p i = π * q i` for some other
sequence `q`. -/
lemma hasSum_mellin_pi_mul {a : ι → ℂ} {q : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hq : ∀ i, a i = 0 ∨ 0 < q i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * rexp (-π * q i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (q i) ^ s.re) :
    HasSum (fun i ↦ π ^ (-s) * Gamma s * a i / q i ^ s) (mellin F s) := by
  have hp i : a i = 0 ∨ 0 < π * q i := by rcases hq i with h | h <;> simp [h, pi_pos]
  convert hasSum_mellin hp hs (by simpa using hF) ?_ using 2 with i
  · have : a i / ↑(π * q i) ^ s = π ^ (-s) * a i / q i ^ s := by
      rcases hq i with h | h
      · simp [h]
      · rw [ofReal_mul, mul_cpow_ofReal_nonneg pi_pos.le h.le, ← div_div, cpow_neg,
          ← div_eq_inv_mul]
    simp_rw [mul_div_assoc, this]
    ring_nf
  · have (i : _) : ‖a i‖ / ↑(π * q i) ^ s.re = π ^ (-s.re) * ‖a i‖ / q i ^ s.re := by
      rcases hq i with h | h
      · simp [h]
      · rw [mul_rpow pi_pos.le h.le, ← div_div, rpow_neg pi_pos.le, ← div_eq_inv_mul]
    simpa only [this, mul_div_assoc] using h_sum.mul_left _

/-- Version allowing some constant terms (which are omitted from the sums). -/
lemma hasSum_mellin_pi_mul₀ {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, 0 ≤ p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ if p i = 0 then 0 else a i * rexp (-π * p i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (p i) ^ s.re) :
    HasSum (fun i ↦ π ^ (-s) * Gamma s * a i / p i ^ s) (mellin F s) := by
  have hs' : s ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs)
  let a' i := if p i = 0 then 0 else a i
  have hp' i : a' i = 0 ∨ 0 < p i := by
    simp only [a']
    split_ifs with h <;> try tauto
    exact Or.inr (lt_of_le_of_ne (hp i) (Ne.symm h))
  have (i t : _) : (if p i = 0 then 0 else a i * rexp (-π * p i * t)) =
      a' i * rexp (-π * p i * t) := by
    simp [a']
  simp_rw [this] at hF
  convert hasSum_mellin_pi_mul hp' hs hF ?_ using 2 with i
  · rcases eq_or_ne (p i) 0 with h | h <;>
    simp [a', h, ofReal_zero, zero_cpow hs', div_zero]
  · refine h_sum.of_norm_bounded (fun i ↦ ?_)
    simp only [a']
    split_ifs
    · simp only [norm_zero, zero_div]
      positivity
    · have := hp i
      rw [norm_of_nonneg (by positivity)]

/-- Tailored version for even Jacobi theta functions. -/
lemma hasSum_mellin_pi_mul_sq {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ if r i = 0 then 0 else a i * rexp (-π * r i ^ 2 * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / |r i| ^ s.re) :
    HasSum (fun i ↦ Gammaℝ s * a i / |r i| ^ s) (mellin F (s / 2)) := by
  have hs' : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  simp_rw [← sq_eq_zero_iff (a := r _)] at hF
  convert hasSum_mellin_pi_mul₀ (fun i ↦ sq_nonneg (r i)) hs' hF ?_ using 3 with i
  · rw [← neg_div, Gammaℝ_def]
  · rw [← sq_abs, ofReal_pow, ← cpow_nat_mul']
    · ring_nf
    all_goals rw [arg_ofReal_of_nonneg (abs_nonneg _)]; linarith [pi_pos]
  · convert h_sum using 3 with i
    rw [← sq_abs, ← rpow_natCast_mul (abs_nonneg _), div_ofNat_re, Nat.cast_ofNat,
      mul_div_cancel₀ _ two_pos.ne']

/-- Tailored version for odd Jacobi theta functions. -/
lemma hasSum_mellin_pi_mul_sq' {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * r i * rexp (-π * r i ^ 2 * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / |r i| ^ s.re) :
    HasSum (fun i ↦ Gammaℝ (s + 1) * a i * SignType.sign (r i) / |r i| ^ s)
    (mellin F ((s + 1) / 2)) := by
  have hs₁ : s ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs)
  have hs₂ : 0 < (s + 1).re := by rw [add_re, one_re]; positivity
  have hs₃ : s + 1 ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs₂)
  have (i t : _) : (a i * r i * rexp (-π * r i ^ 2 * t)) =
      if r i = 0 then 0 else (a i * r i * rexp (-π * r i ^ 2 * t)) := by
    split_ifs with h <;> simp [h]
  conv at hF => enter [t, ht, 1, i]; rw [this]
  convert hasSum_mellin_pi_mul_sq hs₂ hF ?_ using 2 with i
  · rcases eq_or_ne (r i) 0 with h | h
    · rw [h, abs_zero, ofReal_zero, zero_cpow hs₁, zero_cpow hs₃, div_zero, div_zero]
    · rw [cpow_add _ _ (ofReal_ne_zero.mpr <| abs_ne_zero.mpr h), cpow_one]
      conv_rhs => enter [1]; rw [← sign_mul_abs (r i), ofReal_mul, ← ofRealHom_eq_coe,
        SignType.map_cast]
      field_simp [h]
  · convert h_sum using 2 with i
    rcases eq_or_ne (r i) 0 with h | h
    · rw [h, abs_zero, ofReal_zero, zero_rpow hs₂.ne', zero_rpow hs.ne', div_zero, div_zero]
    · rw [add_re, one_re, rpow_add (abs_pos.mpr h), rpow_one, norm_mul, norm_real,
        Real.norm_eq_abs, ← div_div, div_right_comm, mul_div_cancel_right₀ _ (abs_ne_zero.mpr h)]
