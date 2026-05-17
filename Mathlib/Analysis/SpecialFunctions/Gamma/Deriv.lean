/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Derivative of the Gamma function

This file shows that the (complex) `Γ` function is complex-differentiable at all `s : ℂ` with
`s ∉ {-n : n ∈ ℕ}`, as well as the real counterpart.

## Main results

* `Complex.differentiableAt_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `Real.differentiableAt_Gamma`: `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/

public section


noncomputable section

open Filter Set Real Asymptotics
open scoped Topology

namespace Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x)) :=
  funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Mellin
transform of `log t * exp (-t)`. -/
theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  convert (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

@[fun_prop]
theorem differentiableAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ Gamma s := by
  -- We will show, by induction on `n`, that `Gamma` is differentiable on `-n < Re s`.
  suffices ∀ (n : ℕ) (s : ℂ) (hsre : -n < s.re) (hs : ∀ m : ℕ, s ≠ -m), DifferentiableAt ℂ _ s from
    this (⌊-s.re⌋₊ + 1) s (by grind [Nat.lt_floor_add_one (-s.re)]) hs
  intro n s hsre hs
  induction n generalizing s with
  | zero =>
    -- Case `n = 0`: use relation to `gammaIntegral`
    replace hsre : 0 < s.re := by simpa using hsre
    have : IsOpen {s : ℂ | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    apply (hasDerivAt_GammaIntegral (by simpa using hsre)).differentiableAt.congr_of_eventuallyEq
    filter_upwards [this.mem_nhds hsre] with a using Gamma_eq_integral
  | succ n IH =>
    -- Induction step: use recurrence relation
    have hsne : s ≠ 0 := by grind [hs 0]
    specialize IH (s + 1) (by grind [add_re, one_re]) (fun m ↦ by grind [hs (m + 1)])
    have := IH.comp s (show DifferentiableAt ℂ (fun s ↦ s + 1) s by fun_prop)
    apply (this.fun_div differentiableAt_id hsne).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hsne] using by grind [Gamma_add_one]

theorem differentiableAt_Gamma_one : DifferentiableAt ℂ Gamma 1 :=
  differentiableAt_Gamma 1 (by norm_cast; simp)

theorem continuousAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : ContinuousAt Gamma s :=
  (differentiableAt_Gamma s hs).continuousAt

theorem continuousAt_Gamma_one : ContinuousAt Gamma 1 :=
  differentiableAt_Gamma_one.continuousAt

/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
  rw [show 𝓝 (1 : ℂ) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add, Complex.Gamma_one]]
  refine tendsto_nhdsWithin_congr Gamma_add_one (continuousAt_iff_punctured_nhds.mp ?_)
  exact ContinuousAt.comp' (by simp [continuousAt_Gamma_one]) (continuous_add_const 1).continuousAt

theorem not_continuousAt_Gamma_zero : ¬ ContinuousAt Gamma 0 :=
  tendsto_self_mul_Gamma_nhds_zero.not_tendsto (by simp) ∘
    continuousAt_iff_punctured_nhds.mp ∘ continuousAt_id.mul

theorem not_differentiableAt_Gamma_zero : ¬ DifferentiableAt ℂ Gamma 0 :=
  mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

theorem not_continuousAt_Gamma_neg_nat (n : ℕ) : ¬ ContinuousAt Gamma (-n) := by
  induction n
  case zero =>
    rw [Nat.cast_zero, neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose ih
    rw [Nat.cast_add, Nat.cast_one] at ih
    suffices ContinuousAt (fun s ↦ Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s ↦ Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s ↦ s - 1) (continuous_sub_right 1).continuousAt
    rw [← neg_add']
    have h0 : -(n + 1) ≠ (0 : ℂ) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

theorem not_differentiableAt_Gamma_neg_nat (n : ℕ) : ¬ DifferentiableAt ℂ Gamma (-n) :=
  mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

theorem deriv_Gamma_add_one (s : ℂ) (hs : s ≠ 0) :
    deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s := by
  by_cases! h : ∃ m : ℕ, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add, ← neg_sub', ← Nat.cast_one, ← Nat.cast_sub,
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m),
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1)),
      Gamma_neg_nat_eq_zero, zero_add, mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s ↦ Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

end GammaHasDeriv

end Complex

namespace Real

@[fun_prop]
theorem differentiableAt_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ Gamma s := by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  exact hs

theorem differentiableOn_Gamma_Ioi : DifferentiableOn ℝ Gamma (Ioi 0) :=
  fun _ h ↦ (differentiableAt_Gamma <| by bound [mem_Ioi.mp h]).differentiableWithinAt

end Real
