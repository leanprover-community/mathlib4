/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

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
* `HasIndepIncrements.isPreBrownianReal_of_hasLaw`: A stochastic process `X` with independent
  increments and such that for all `t`, `X t` has law `gaussianReal 0 t` is a pre-Brownian motion.
* `IsPreBrownianReal.indepFun_shift`: The weak Markov property: If `B` is a pre-Brownian motion,
  then `B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.

## Tags

pre-Brownian motion, Brownian motion, Markov property

-/

@[expose] public section

open MeasureTheory ProbabilityTheory.BrownianReal
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

/-! ### Pre-Brownian motion -/

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `projectiveFamily`.

Note: we name the constructor `mk'` so as to define later `IsPreBrownianReal.mk`, which to
pre-Brownian motion will associate a continuous modification,
in a way similar to `AEMeasurable.mk`. -/
structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P

/- A modification of a pre-Brownian is pre-Brownian. -/
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

lemma IsPreBrownianReal.eval_zero_ae_eq_zero (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, B 0 ω = 0 := by
  have := hB.hasLaw_eval 0
  rw [gaussianReal_zero_var] at this
  exact this.ae_eq_of_dirac

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
  convert (hB.hasLaw {s, t}).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := fun x ↦ x ⟨t, by simp⟩) ?_ ?_
  · simp
  · simp
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

/-- A pre-Brownian motion has independent increments. -/
lemma IsPreBrownianReal.hasIndepIncrements (hB : IsPreBrownianReal B P) :
    HasIndepIncrements B P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht ↦ hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij ↦ ?_
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by grind), min_comm]
      grind
    have h1 : i.succ ≤ j.succ := Fin.strictMono_succ h |>.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- A stochastic process `X` with independent increments and such that for all `t`, `X t`
has law `gaussianReal 0 t` is a pre-Brownian motion. -/
theorem HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownianReal X P := by
  have h0 : ∀ᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.ae_eq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact incr.isGaussianProcess (fun t ↦ (law t).hasGaussianLaw) h0
  · rw [(law t).integral_eq, integral_id_gaussianReal]
  have h1 := incr.indepFun_eval_sub zero_le hst h0
  have := (law 0).isProbabilityMeasure
  have h2 : X t = X t - X s + X s := by simp
  rw [h2, covariance_add_right, h1.covariance_eq_zero, covariance_self, (law s).variance_eq,
    variance_id_gaussianReal]
  · simp
  · exact (law s).aemeasurable
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two

lemma IsPreBrownianReal.neg (hB : IsPreBrownianReal B P) : IsPreBrownianReal (-B) P := by
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_) (fun n t ht ↦ ?_)
  · simpa using gaussianReal_neg (hB.hasLaw_eval t)
  convert (hB.hasIndepIncrements n t ht).comp (fun _ x ↦ -x) (by fun_prop)
  simp
  grind

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

/-! ### Brownian motion -/

variable {B X : ℝ≥0 → Ω → ℝ}

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `IsPreBrownianReal`, and if it has almost-surely continuous paths. -/
structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

lemma IsBrownianReal.neg (hB : IsBrownianReal B P) :
    IsBrownianReal (-B) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ ↦ by simpa [← Pi.neg_def, continuous_neg_iff])

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
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

end IsBrownianReal

end ProbabilityTheory
