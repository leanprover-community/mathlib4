/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The Schwartz space on `ℝ` is second countable

We show that `𝓢(ℝ, F)` is second countable (hence separable) whenever `F` is.

The Schwartz seminorm `f ↦ sup_x |x| ^ k * ‖f⁽ⁿ⁾ x‖` is bounded by the `L¹` norm of the
derivative of `x ↦ x ^ k • f⁽ⁿ⁾ x`, since a Schwartz function on `ℝ` is bounded pointwise by the
`L¹` norm of its derivative. Hence the continuous linear map sending `f` to the family of these
derivatives in `ℕ × ℕ → L¹(ℝ, F)` is an inducing map into a second countable space.

## Main statements

* `SchwartzMap.norm_le_integral_norm_deriv`: `‖f x‖ ≤ ∫ y, ‖deriv f y‖` for `f : 𝓢(ℝ, F)`.
* `SchwartzMap.derivCLM_pow_apply`: the `n`-th power of `SchwartzMap.derivCLM` is the `n`-th
  iterated derivative.
* `SchwartzMap.instSecondCountableTopology`: `𝓢(ℝ, F)` is second countable if `F` is. In
  particular, `𝓢(ℝ, F)` is a separable space.

## TODO

Extend the result to `𝓢(E, F)` for a finite-dimensional real normed space `E`.
-/

public noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Schwartz function on `ℝ` is bounded pointwise by the `L¹` norm of its derivative. -/
theorem norm_le_integral_norm_deriv (f : 𝓢(ℝ, F)) (x : ℝ) : ‖f x‖ ≤ ∫ y, ‖deriv f y‖ := by
  obtain ⟨ℓ, hℓ, hℓx⟩ := exists_dual_vector'' ℝ (f x)
  have hint : Integrable (deriv f) := (derivCLM ℝ F f).integrable
  have hlim : Tendsto (fun y ↦ ℓ (f y)) atBot (𝓝 0) := by
    have := (ℓ.continuous.tendsto 0).comp (f.tendsto_cocompact.mono_left atBot_le_cocompact)
    rwa [map_zero] at this
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := x)
    (fun y _ ↦ ℓ.hasFDerivAt.comp_hasDerivAt y (f.hasDerivAt y))
    (ℓ.integrable_comp hint).integrableOn hlim
  simp only [Function.comp_apply, sub_zero, hℓx] at h
  calc ‖f x‖ = ∫ y in Iic x, ℓ (deriv f y) := by simpa using h.symm
    _ ≤ ∫ y in Iic x, ‖deriv f y‖ := by
      refine setIntegral_mono (ℓ.integrable_comp hint).integrableOn hint.norm.integrableOn
        fun y ↦ ?_
      exact (le_abs_self _).trans ((ℓ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hℓ))
    _ ≤ ∫ y, ‖deriv f y‖ :=
      setIntegral_le_integral hint.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)

/-- The `n`-th power of `SchwartzMap.derivCLM` is the `n`-th iterated derivative. -/
@[simp]
theorem derivCLM_pow_apply (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝓢(ℝ, F))
    (x : ℝ) : (derivCLM 𝕜 F ^ n) f x = iteratedDeriv n f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change (derivCLM 𝕜 F ^ n) (derivCLM 𝕜 F f) x = _
    rw [ih, iteratedDeriv_succ']
    rfl

/-- The map `f ↦ x ^ k • f⁽ⁿ⁾`, indexed by `(k, n)`. -/
private def momentDerivCLM (c : ℕ × ℕ) : 𝓢(ℝ, F) →L[ℝ] 𝓢(ℝ, F) :=
  (smulLeftCLM F (fun x : ℝ ↦ x ^ c.1)).comp (derivCLM ℝ F ^ c.2)

private theorem momentDerivCLM_apply (c : ℕ × ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    momentDerivCLM c f x = x ^ c.1 • iteratedDeriv c.2 f x := by
  have hg : Function.HasTemperateGrowth (fun x : ℝ ↦ x ^ c.1) := by fun_prop
  simp [momentDerivCLM, hg]

/-- The map sending `f` to the family of derivatives of `x ↦ x ^ k • f⁽ⁿ⁾ x`, seen in `L¹`. -/
private def embedding : 𝓢(ℝ, F) →L[ℝ] (ℕ × ℕ → Lp F 1 (volume : Measure ℝ)) :=
  ContinuousLinearMap.pi fun c ↦
    (toLpCLM ℝ F 1 volume).comp ((derivCLM ℝ F).comp (momentDerivCLM c))

private theorem seminorm_le_norm_embedding (c : ℕ × ℕ) (f : 𝓢(ℝ, F)) :
    schwartzSeminormFamily ℝ ℝ F c f ≤ ‖embedding f c‖ := by
  have hnorm : ‖embedding f c‖ = ∫ y, ‖deriv (momentDerivCLM c f) y‖ := by
    simp [embedding, norm_toLp_one]
  rw [hnorm]
  refine seminorm_le_bound' ℝ c.1 c.2 f (integral_nonneg fun _ ↦ norm_nonneg _) fun x ↦ ?_
  have := norm_le_integral_norm_deriv (momentDerivCLM c f) x
  rwa [momentDerivCLM_apply, norm_smul, norm_pow, Real.norm_eq_abs] at this

private theorem isInducing_embedding : IsInducing (embedding (F := F)) := by
  refine isInducing_iff_nhds.2 fun f ↦ le_antisymm (embedding.continuous.tendsto f).le_comap ?_
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ ℝ F).mem_nhds_iff f U).1 hU
  refine ⟨⋂ c ∈ s, (fun v ↦ v c) ⁻¹' Metric.ball (embedding f c) r,
    (biInter_finset_mem s).2 fun c _ ↦
      (continuous_apply c).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr),
    fun g hg ↦ hsub ?_⟩
  simp only [mem_preimage, mem_iInter, Metric.mem_ball, dist_eq_norm] at hg
  rw [Seminorm.mem_ball]
  refine Seminorm.finset_sup_apply_lt hr fun c hc ↦ (seminorm_le_norm_embedding c _).trans_lt ?_
  simpa using hg c hc

/-- The Schwartz space `𝓢(ℝ, F)` is second countable (hence separable) when `F` is. -/
instance instSecondCountableTopology [SecondCountableTopology F] :
    SecondCountableTopology 𝓢(ℝ, F) :=
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  isInducing_embedding.secondCountableTopology

end SchwartzMap
