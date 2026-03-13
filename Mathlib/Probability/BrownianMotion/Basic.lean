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
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of a Brownian motion, see `gaussianProjectiveFamily`. -/
structure IsPreBrownian (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (gaussianProjectiveFamily I) P

lemma IsPreBrownian.congr {Y : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownian X P) (h : ∀ t, X t =ᵐ[P] Y t) :
    IsPreBrownian Y P where
  hasLaw I := by
    refine (hX.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, X i ω = Y i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

lemma IsPreBrownian.isGaussianProcess (hX : IsPreBrownian X P) : IsGaussianProcess X P where
  hasGaussianLaw I := (hX.hasLaw I).hasGaussianLaw

lemma IsPreBrownian.aemeasurable (hX : IsPreBrownian X P) (t : ℝ≥0) : AEMeasurable (X t) P :=
  HasGaussianLaw.aemeasurable (hX.isGaussianProcess.hasGaussianLaw_eval t)

lemma IsPreBrownian.hasLaw_eval (hX : IsPreBrownian X P) (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_gaussianProjectiveFamily ⟨t, by simp⟩).hasLaw.comp (hX.hasLaw {t})

lemma IsPreBrownian.hasLaw_sub (hX : IsPreBrownian X P) (s t : ℝ≥0) :
    HasLaw (X s - X t) (gaussianReal 0 (max (s - t) (t - s))) P :=
  (measurePreserving_eval_sub_eval_gaussianProjectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hX.hasLaw _)

lemma IsPreBrownian.integral_eval (hX : IsPreBrownian X P) (t : ℝ≥0) :
    P[X t] = 0 := by
  rw [(hX.hasLaw_eval t).integral_eq, integral_id_gaussianReal]

lemma IsPreBrownian.integrable_eval (hX : IsPreBrownian X P) (t : ℝ≥0) :
    Integrable (X t) P := (hX.isGaussianProcess.hasGaussianLaw_eval t).integrable

lemma IsPreBrownian.covariance_eval (hX : IsPreBrownian X P) (s t : ℝ≥0) :
    cov[X s, X t; P] = min s t := by
  convert (hX.hasLaw {s, t}).covariance_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_gaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsPreBrownian.covariance_fun_eval (hX : IsPreBrownian X P) (s t : ℝ≥0) :
    cov[fun ω ↦ X s ω, fun ω ↦ X t ω; P] = min s t :=
  hX.covariance_eval s t

set_option backward.isDefEq.respectTransparency false in
lemma IsGaussianProcess.isPreBrownian_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownian X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have : IsGaussian
        (Measure.map (⇑(PiLp.continuousLinearEquiv 2 ℝ fun a ↦ ℝ).symm)
        (Measure.map (fun ω ↦ I.restrict fun x ↦ X x ω) P)) := by
      have := (h1.hasGaussianLaw I).isGaussian_map
      infer_instance
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [PiLp.continuousLinearEquiv_symm_apply, id_eq]
        simp_rw [← PiLp.continuousLinearEquiv_symm_apply 2 ℝ, ← ContinuousLinearEquiv.coe_coe]
        rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily,
          ContinuousLinearMap.integral_comp_comm]
        · simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply]
          congr with i
          rw [eval_integral]
          · simpa using h2 _
          · exact fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
        · exact Integrable.of_eval fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
        · exact IsGaussian.integrable_id
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x ↦ ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      have : IsFiniteMeasure (Measure.map (fun ω ↦ I.restrict fun x ↦ X x ω) P) := by
        have := (h1.hasGaussianLaw I).isGaussian_map
        infer_instance
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
lemma IsPreBrownian.smul (hX : IsPreBrownian X P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownian (fun t ω ↦ (X (c * t) ω) / √c) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : X (c * t) ω / √c = (1 / √c) • ((X ∘ (c * ·)) t ω) := by
      simp [inv_mul_eq_div]
    simp_rw [this]
    exact (IsGaussianProcess.comp_right hX.isGaussianProcess _).smul _
  · rw [integral_div, hX.integral_eval, zero_div]
  · rw [covariance_fun_div_left, covariance_fun_div_right, hX.covariance_eval,
      min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that it is pre-Brownian, see `IsPreBrownian.indepFun_shift` for independence. -/
lemma IsPreBrownian.shift (hX : IsPreBrownian X P) (t₀ : ℝ≥0) :
    IsPreBrownian (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P := by
  refine (hX.isGaussianProcess.shift t₀).isPreBrownian_of_covariance (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · rw [integral_sub, hX.integral_eval, hX.integral_eval, sub_zero]
    all_goals exact (hX.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hX.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hX.covariance_eval, hX.covariance_eval, hX.covariance_eval, hX.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (hX.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hX.isGaussianProcess.hasGaussianLaw_sub.memLp_two

set_option backward.isDefEq.respectTransparency false in
/-- **Weak Markov property**: If `X` is a pre-Brownian motion, then
`X (t₀ + t) - X t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that of independence, see `IsPreBrownian.shift` for the proof
that it is pre-Brownian. -/
lemma IsPreBrownian.indepFun_shift (hX : IsPreBrownian X P) --(mX : ∀ t, Measurable (X t))
    (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ X (t₀ + t) ω - X t₀ ω) (fun ω (t : Set.Iic t₀) ↦ X t ω) P := by
  have mX t := hX.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hX.isGaussianProcess.of_isGaussianProcess
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
    have := hX.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, hX.covariance_eval, hX.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hX.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

set_option backward.isDefEq.respectTransparency false in
lemma IsPreBrownian.inv (hX : IsPreBrownian X P) :
    IsPreBrownian (fun t ω ↦ t * (X (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownian_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact (IsGaussianProcess.comp_right hX.isGaussianProcess _).smul _
  · rw [integral_const_mul, hX.integral_eval, mul_zero]
  · have := hX.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left, covariance_const_mul_right, hX.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end ProbabilityTheory
