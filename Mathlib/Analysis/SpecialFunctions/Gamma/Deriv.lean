/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

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


noncomputable section

open Filter Set Real Asymptotics
open scoped Topology

namespace Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x ↦ ↑(Real.exp (-x)) :=
  funext fun s ↦ by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Mellin
transform of `log t * exp (-t)`. -/
theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  convert (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [Complex.norm_eq_abs, abs_ofReal, ← Real.norm_eq_abs, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

theorem differentiableAt_GammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ (GammaAux n) s := by
  induction' n with n hn generalizing s
  · refine (hasDerivAt_GammaIntegral ?_).differentiableAt
    rw [Nat.cast_zero] at h1; linarith
  · dsimp only [GammaAux]
    specialize hn (s + 1)
    have a : 1 - (s + 1).re < ↑n := by
      rw [Nat.cast_succ] at h1; rw [Complex.add_re, Complex.one_re]; linarith
    have b : ∀ m : ℕ, s + 1 ≠ -m := by
      intro m; have := h2 (1 + m)
      contrapose! this
      rw [← eq_sub_iff_add_eq] at this
      simpa using this
    refine DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) ?_) ?_ ?_
    · rw [differentiableAt_add_const_iff (1 : ℂ)]; exact differentiableAt_id
    · exact differentiableAt_id
    · simpa using h2 0

theorem differentiableAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ Gamma s := by
  let n := ⌊1 - s.re⌋₊ + 1
  have hn : 1 - s.re < n := mod_cast Nat.lt_floor_add_one (1 - s.re)
  apply (differentiableAt_GammaAux s n hn hs).congr_of_eventuallyEq
  let S := {t : ℂ | 1 - t.re < n}
  have : S ∈ 𝓝 s := by
    rw [mem_nhds_iff]; use S
    refine ⟨Subset.rfl, ?_, hn⟩
    have : S = re ⁻¹' Ioi (1 - n : ℝ) := by
      ext; rw [preimage, Ioi, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq]; exact sub_lt_comm
    rw [this]
    exact Continuous.isOpen_preimage continuous_re _ isOpen_Ioi
  apply eventuallyEq_of_mem this
  intro t ht; rw [mem_setOf_eq] at ht
  apply Gamma_eq_GammaAux; linarith

end GammaHasDeriv

/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
  rw [show 𝓝 (1 : ℂ) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add, Complex.Gamma_one]]
  convert (Tendsto.mono_left _ nhdsWithin_le_nhds).congr'
    (eventuallyEq_of_mem self_mem_nhdsWithin Complex.Gamma_add_one) using 1
  refine ContinuousAt.comp (g := Gamma) ?_ (continuous_id.add continuous_const).continuousAt
  refine (Complex.differentiableAt_Gamma _ fun m ↦ ?_).continuousAt
  rw [zero_add, ← ofReal_natCast, ← ofReal_neg, ← ofReal_one, Ne, ofReal_inj]
  refine (lt_of_le_of_lt ?_ zero_lt_one).ne'
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

end Complex

namespace Real

theorem differentiableAt_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ Gamma s := by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  exact hs

end Real
