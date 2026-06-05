/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Process.Filtration

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne

/-!
# Brownian motion

In this file we define two predicates over stochastic processes `X : ℝ≥0 → Ω → ℝ` given
a probability measure `P : Measure Ω`. `IsPreBrownianReal X P` means that
`X` is a pre-Brownian motion. It means that it has the law of the Brownian motion, namely that
its finite dimensional distributions are given by `projectiveFamily`. Then
`IsBrownianReal X P` means that `X` is a Brownian motion, which means that it is a pre-Brownian
motion with almost surely continuous paths.

We prove that a centered Gaussian process `X` with covariances given by `cov[X s, X t; P] = min s t`
is a pre-Brownian motion and provide basic invariance properties. We also prove the
weak Markov property: if `B` is a pre-Brownian motion and `t₀ : ℝ≥0`, then the process
`t ↦ B (t + t₀) - B t₀` is a pre-Brownian motion independent from `(B t | t ≤ t₀)`.

## Main definitions

* `IsPreBrownianReal X P`: A stochastic process is called pre-Brownian if its finite-dimensional
  laws are those of the Brownian motion, see `projectiveFamily`.
* `IsBrownianReal X P`: A stochastic process is called Brownian if its finite-dimensional laws
  are those of the Brownian motion, see `IsPreBrownianReal`,
  and if it has almost-surely continuous paths.

## Main statements

* `IsGaussianProcess.isPreBrownianReal_of_covariance`: A centered Gaussian process with the right
  covariance is a pre-Brownian motion.
* `IsPreBrownianReal.indepFun_shift`: The weak Markov property: If `B` is a pre-Brownian motion,
  then `B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
* `IsBrownianReal.measure_eq_zero_or_one_of_measurableSet_rightCont_zero`:
  **Blumenthal's zero-one law**: Let `𝓕` be the canonical filtration associated to a Brownian
  motion. Then the `σ`-algebra `⨅ s > 0, 𝓕 s` is trivial.

## Tags

pre-Brownian motion, Brownian motion, Markov property

-/

@[expose] public section

open MeasureTheory Filtration MeasurableSpace Filter ProbabilityTheory.BrownianReal
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `projectiveFamily`.

Note: we name the constructor `mk'` so as to define later `IsPreBrownianReal.mk`, which to
pre-Brownian motion will associate a continuous modification,
in a way similar to `AEMeasurable.mk`. -/
structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P

lemma IsPreBrownianReal.congr {C : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ∀ t, B t =ᵐ[P] C t) :
    IsPreBrownianReal C P where
  hasLaw I := by
    refine (hB.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, B i ω = C i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm

lemma IsPreBrownianReal.isGaussianProcess (hB : IsPreBrownianReal B P) : IsGaussianProcess B P where
  hasGaussianLaw I := (hB.hasLaw I).hasGaussianLaw

lemma IsPreBrownianReal.aemeasurable (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    AEMeasurable (B t) P :=
  HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)

lemma IsPreBrownianReal.hasLaw_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})

lemma IsPreBrownianReal.hasLaw_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  (measurePreserving_eval_sub_eval_projectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)

lemma IsPreBrownianReal.integral_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    P[B t] = 0 := by
  rw [(hB.hasLaw_eval t).integral_eq, integral_id_gaussianReal]

lemma IsPreBrownianReal.integrable_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Integrable (B t) P := (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable

lemma IsPreBrownianReal.covariance_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = min s t := by
  convert (hB.hasLaw {s, t}).covariance_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

lemma IsPreBrownianReal.covariance_fun_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[fun ω ↦ B s ω, fun ω ↦ B t ω; P] = min s t :=
  hB.covariance_eval s t

/-- A centered Gaussian process with the right covariance is a pre-Brownian motion. -/
theorem IsGaussianProcess.isPreBrownianReal_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownianReal X P where
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
        simp only [PiLp.continuousLinearEquiv_symm_apply, integral_id_projectiveFamily,
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
        rw [covariance_eval_projectiveFamily, covariance_map]
        · wlog hij : i.1 ≤ j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      · exact fun i ↦ (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i ↦ ((h1.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

/-- If `B` is a pre-Brownian motion and `c > 0`, then
`t ↦ (√c)⁻¹ B (c t)` is a pre-Brownian motion. -/
lemma IsPreBrownianReal.smul (hB : IsPreBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [this]
    exact (hB.isGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval, min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

/-- **Weak Markov property**: If `B` is a pre-Brownian motion, then
`t ↦ B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that it is pre-Brownian,
see `IsPreBrownianReal.indepFun_shift` for independence. -/
lemma IsPreBrownianReal.shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IsPreBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P := by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownianReal_of_covariance
    (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-- **Weak Markov property**: If `B` is a pre-Brownian motion, then
`B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof of independence, see `IsPreBrownianReal.shift` for the proof
that it is pre-Brownian. -/
lemma IsPreBrownianReal.indepFun_shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) ↦ B t ω) P := by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{t},
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t ≤ t₀⟩
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, hB.covariance_eval, hB.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- If `B` is a pre-Brownian motion then `t ↦ t * B (1 / t)` is a pre-Brownian motion. -/
lemma IsPreBrownianReal.inv (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * (B (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
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

end IsPreBrownianReal

section IsBrownianReal

variable {B X : ℝ≥0 → Ω → ℝ}

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `IsPreBrownianReal`, and if it has almost-surely continuous paths. -/
structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

/-- If `B` is a Brownian motion and `c > 0`, then `t ↦ (√c)⁻¹ B (c t)` is a Brownian motion. -/
lemma IsBrownianReal.smul (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

lemma IsBrownianReal.shift (hB : IsBrownianReal B P) (t₀ : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop

lemma IsBrownianReal.tendsto_nhds_zero (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (B · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [hB.cont, (hB.hasLaw_eval 0).ae_eq_const_of_gaussianReal] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

end IsBrownianReal

section Blumenthal

variable (mB : ∀ t, Measurable (B t))

local notation "𝓕" => (natural B (fun t ↦ Measurable.stronglyMeasurable (mB t)))₊ 0

/-- **Blumenthal's zero-one law**: Let `𝓕` be the canonical filtration associated to a Brownian
motion. Then the `σ`-algebra `⨅ s > 0, 𝓕 s` is trivial. -/
lemma IsBrownianReal.measure_eq_zero_or_one_of_measurableSet_rightCont_zero
    (hB : IsBrownianReal B P) (cB : ∀ ω, Continuous (B · ω)) {A : Set Ω} (hA : MeasurableSet[𝓕] A) :
    P A = 0 ∨ P A = 1 := by
  have 𝓕_eq : 𝓕 = ⨅ s > (0 : ℝ≥0), (.comap (fun ω (t : Set.Iic s) ↦ B t ω) inferInstance) := by
    simp_rw [rightCont_eq, natural_eq_comap]
  have := hB.isGaussianProcess.isProbabilityMeasure
  -- We consider three different `σ`-algebras. `m1` is the one generated by the process `B`.
  let m1 : MeasurableSpace Ω := .comap (fun ω t ↦ B t ω) inferInstance
  -- `m2` is the one generated by the restriction of `B` to positive real numbers.
  let m2 : MeasurableSpace Ω := .comap (fun ω (t : Set.Ioi (0 : ℝ≥0)) ↦ B t ω) inferInstance
  -- `𝓕` is `⨅ s > 0, 𝓕 s`, which we want to show to be trivial.
  let mΩ := mΩ -- so that `mΩ` is the sigma-algebra synthesized by typeclass inference
-- We easily have that `𝓕 ≤ m1 ≤ mΩ`.
  have hm1 : m1 ≤ mΩ := (measurable_pi_lambda _ mB).comap_le
  have h𝓕 : 𝓕 ≤ m1 := by
    rw [𝓕_eq]
    exact iInf₂_le_of_le 1 (by simp) <|
      comap_le_comap_of_eq_comp (fun x t ↦ x t.1) (by fun_prop) (by grind)
  have h𝓕' := h𝓕.trans hm1
  -- Because `B` is continuous, `B t ⟶ B 0` as `t → 0⁺`, thus
  -- the random variable `B 0` is actually measurable with respect to `m2`, so `m1 ≤ m2`.
  have : m1 ≤ m2 := by
    simp_rw [m1, m2, comap_process_pi]
    rw [iSup_split_single _ 0, sup_le_iff]
    constructor; swap
    · simp_rw [← pos_iff_ne_zero, iSup_subtype, Set.mem_Ioi]
      rfl
    rw [← measurable_iff_comap_le]
    have : NeBot ((𝓝[≠] (0 : ℝ≥0)).comap ((↑) : Set.Ioi (0 : ℝ≥0) → ℝ≥0)) := by
      refine comap_coe_neBot_of_le_principal <| le_principal_iff.2 ?_
      convert self_mem_nhdsWithin
      ext; simp [pos_iff_ne_zero]
    refine @measurable_of_tendsto_metrizable' _ _ (iSup _) _ _ _ _ _ _ _ _ this _
      (fun t ↦ (comap_measurable _).iSup' t) ?_
    refine Filter.tendsto_comap'_iff ?_ |>.2
      (tendsto_pi_nhds.2 fun ω ↦ continuousAt_iff_punctured_nhds.1 (cB ω).continuousAt)
    convert self_mem_nhdsWithin
    ext; simp [pos_iff_ne_zero]
  -- We prove the result by showing that `𝓕` is independent of itself.
  refine measure_eq_zero_or_one_of_indep_self ?_ hA
  -- To do so, we show that for all `A ∈ 𝓕`, all finite sets `I ⊆ (0, +∞)` and all
  -- bounded continuous functions `f : (I → ℝ) → ℝ`,
  -- `∫ ω in A, f (fun t ↦ B t) ∂P = P.real A * ∫ ω, f (fun t ↦ B t) ∂P`.
  refine indep_of_indep_of_le_right ?_ (h𝓕.trans this)
  refine indep_comap_process_of_bcf h𝓕' (fun _ ↦ (mB _).aemeasurable) fun A hA I f ↦ ?_
  -- If `I` is empty, there is nothing to do.
  obtain rfl | hI := I.eq_empty_or_nonempty
  · have : Subsingleton ((∅ : Finset (Set.Ioi (0 : ℝ≥0))) → ℝ) := inferInstance
    simp [this.eq_zero]
  -- We now assume `I` is not empty. We then prove that for all `ε > 0` such that `ε ≤ min I`,
  -- `∫ ω in A, f (fun t ↦ B t ω - B ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ B t ω - B ε ω) ∂P`.
  -- This follows from the fact that, because `A ∈ 𝓕` in particular `A` is measurable
  -- with respect to `σ(B t | t ≤ ε)`. This `σ`-algebra is independent from
  -- `σ(B (ε + t) - B ε | t ≥ 0)` by the weak Markov property.
  have key1 (ε : ℝ≥0) (hε1 : 0 < ε) (hε2 : ε ≤ I.min' hI) :
      ∫ ω in A, f (fun t ↦ B t ω - B ε ω) ∂P = P.real A * ∫ ω, f (fun t ↦ B t ω - B ε ω) ∂P := by
    rw [Indep.setIntegral_eq_mul h𝓕' _ (by fun_prop) hA (by fun_prop)]
    refine indep_of_indep_of_le (hB.indepFun_shift ε).symm ?_ ?_
    · rw [𝓕_eq]
      apply iInf₂_le_of_le ε hε1
      rfl
    apply comap_le_comap_of_eq_comp (fun x t ↦ x (t.1 - ε)) (by fun_prop)
    ext ω t
    simp only [Function.comp_apply, sub_left_inj]
    rw [add_tsub_cancel_of_le (hε2.trans (I.min'_le t.1 t.2))]
  -- Because `f` is continuous and `B t ⟶ 0` almost surely as `t → 0`,
  -- we deduce that almost surely `f (fun t ↦ B t - B ε) ⟶ f (fun t ↦ B t)` as `ε → 0⁺`.
  have key2 : ∀ᵐ ω ∂P, Tendsto (fun ε ↦ f (fun t ↦ B t ω - B ε ω)) (𝓝[>] 0)
      (𝓝 (f (fun t ↦ B t ω))) := by
    filter_upwards [hB.tendsto_nhds_zero] with ω hω
    refine f.continuous.tendsto _ |>.comp (tendsto_pi_nhds.2 fun t ↦ ?_)
    convert (tendsto_nhdsWithin_of_tendsto_nhds hω).const_sub (B t ω)
    simp
  -- Because `f` is also bounded, we can apply the dominated convergence theorem to show that
  -- `∫ ω in A, f (fun t ↦ B t ω - B ε ω) ∂P ⟶ ∫ ω in A, f (fun t ↦ B t ω) ∂P`
  -- as `ε → 0⁺`.
  have h1 : Tendsto (fun ε ↦ ∫ ω in A, f (fun t ↦ B t ω - B ε ω) ∂P) (𝓝[>] 0)
      (𝓝 (∫ ω in A, f (fun t ↦ B t ω) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
      (integrable_const _) (ae_restrict_of_ae key2)
    · exact .of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
    · exact .of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _
  -- But similarly we have that
  -- `P.real A * ∫ ω, f (fun t ↦ B t ω - B ε ω) ∂P ⟶ P.real A * ∫ ω in A, f (fun t ↦ B t ω) ∂P`
  -- as `ε → 0⁺`, and we can conclude by uniqueness of the limit.
  refine tendsto_nhds_unique h1 ?_
  refine Tendsto.congr' (f₁ := fun ε ↦ P.real A * ∫ ω, f (fun t ↦ B t ω - B ε ω) ∂P) ?_ ?_
  · apply mem_of_superset (Ioc_mem_nhdsGT (I.min' hI).2)
    rintro ε ⟨h1, h2⟩
    exact (key1 ε h1 h2).symm
  refine Filter.Tendsto.const_mul (b := P.real A) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) key2
  · exact .of_forall fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop)
  · exact .of_forall fun _ ↦ ae_of_all _ fun _ ↦ f.norm_coe_le_norm _

end Blumenthal

end ProbabilityTheory
