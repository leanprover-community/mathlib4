/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Brownian motion

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownian

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `gaussianProjectiveFamily`. -/
structure IsPreBrownian (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P

lemma IsPreBrownian.congr {C : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownian B P) (h : ∀ t, B t =ᵐ[P] C t) :
    IsPreBrownian C P where
  hasLaw I := by
    refine (hB.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, B i ω = C i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

lemma IsPreBrownian.isGaussianProcess (hB : IsPreBrownian B P) : IsGaussianProcess B P where
  hasGaussianLaw I := (hB.hasLaw I).hasGaussianLaw

lemma IsPreBrownian.aemeasurable (hB : IsPreBrownian B P) (t : ℝ≥0) : AEMeasurable (B t) P :=
  HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)

lemma IsPreBrownian.hasLaw_eval (hB : IsPreBrownian B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_gaussianProjectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})

lemma IsPreBrownian.hasLaw_sub (hB : IsPreBrownian B P) (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (max (s - t) (t - s))) P :=
  (measurePreserving_eval_sub_eval_gaussianProjectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)

lemma IsPreBrownian.integral_eval (hB : IsPreBrownian B P) (t : ℝ≥0) :
    P[B t] = 0 := by
  rw [(hB.hasLaw_eval t).integral_eq, integral_id_gaussianReal]

lemma IsPreBrownian.integrable_eval (hB : IsPreBrownian B P) (t : ℝ≥0) :
    Integrable (B t) P := (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable

lemma IsPreBrownian.covariance_eval (hB : IsPreBrownian B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = min s t := by
  convert (hB.hasLaw {s, t}).covariance_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsPreBrownian.covariance_fun_eval (hB : IsPreBrownian B P) (s t : ℝ≥0) :
    cov[fun ω ↦ B s ω, fun ω ↦ B t ω; P] = min s t :=
  hB.covariance_eval s t

set_option backward.isDefEq.respectTransparency false in
/-- A centered Gaussian process with the right covariance is a pre-Brownian motion. -/
theorem IsGaussianProcess.isPreBrownian_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownian X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have := (h1.hasGaussianLaw I).isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [id_eq]
        rw [ContinuousLinearEquiv.integral_comp_id_comm,
          ContinuousLinearEquiv.integral_comp_comm]
        simp only [PiLp.continuousLinearEquiv_symm_apply, integral_id_gaussianProjectiveFamily,
          WithLp.toLp_zero, WithLp.toLp_eq_zero]
        congr with i
        rw [eval_integral]
        · simpa using h2 _
        · exact fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x ↦ ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_eval_gaussianProjectiveFamily, covariance_map]
        · wlog hij : i.1 ≤ j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      · exact fun i ↦ (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i ↦ ((h1.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.smul (hB : IsPreBrownian B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownian (fun t ω ↦ (B (c * t) ω) / √c) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : B (c * t) ω / √c = (1 / √c) • ((B ∘ (c * ·)) t ω) := by
      simp [inv_mul_eq_div]
    simp_rw [this]
    exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_div, hB.integral_eval, zero_div]
  · rw [covariance_fun_div_left, covariance_fun_div_right, hB.covariance_eval,
      min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that it is pre-Brownian, see `IsPreBrownian.indepFun_shift` for independence. -/
lemma IsPreBrownian.shift (hB : IsPreBrownian B P) (t₀ : ℝ≥0) :
    IsPreBrownian (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P := by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownian_of_covariance (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that of independence, see `IsPreBrownian.shift` for the proof
that it is pre-Brownian. -/
lemma IsPreBrownian.indepFun_shift (hB : IsPreBrownian B P) --(mX : ∀ t, Measurable (X t))
    (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) ↦ B t ω) P := by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · let L : (({t₀, t₀ + t} : Finset ℝ≥0) → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }
      exact ⟨_, L, fun ω ↦ by simp [L]⟩
    · let L : (({t} : Finset ℝ≥0) → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }
      exact ⟨_, L, fun ω ↦ by simp [L]⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t ≤ t₀⟩
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, hB.covariance_eval, hB.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.inv (hB : IsPreBrownian B P) :
    IsPreBrownian (fun t ω ↦ t * (B (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end IsPreBrownian

section IsBrownian

variable {B X : ℝ≥0 → Ω → ℝ}

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `IsPreBrownian`, and if it has almost-sure continuous paths. -/
structure IsBrownian (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownian X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

lemma IsBrownian.smul (hB : IsBrownian B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (B (c * t) ω) / √c) P where
  toIsPreBrownian := hB.toIsPreBrownian.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

lemma IsBrownian.shift (hB : IsBrownian B P) (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P where
  toIsPreBrownian := hB.toIsPreBrownian.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

lemma IsBrownian.tendsto_nhds_zero (hB : IsBrownian B P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (B · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [hB.cont, (hB.hasLaw_eval 0).ae_eq_const_of_gaussianReal] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

end IsBrownian

end ProbabilityTheory
