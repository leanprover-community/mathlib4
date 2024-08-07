/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib

/-!
# Weak Derivatives


## Tags

weak derivative

-/

open Filter Asymptotics ContinuousLinearMap Set Metric MeasureTheory

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

section

-- variable {ℝ : Type*} [RCLike ℝ] -- maybe make ℝ?
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']

/-- A function `f` has the continuous linear map `f'` as derivative weak derivative ... -/
structure HasWeakFDerivOn (f : E → F) (f' : E → E →L[ℝ] F) (s : Set E) (μ : Measure E) : Prop where
  locallyIntegrable : LocallyIntegrableOn f s μ
  locallyIntegrable_deriv : LocallyIntegrableOn f' s μ
  integral_eq : ∀ ϕ : E → ℝ, ContDiff ℝ ⊤ ϕ → HasCompactSupport ϕ →
    Function.support ϕ ⊆ interior s →
    ∫ x, ϕ x • f' x ∂μ = - ∫ x, smulRightL ℝ E F (fderiv ℝ ϕ x) (f x) ∂μ

@[fun_prop]
def HasWeakFDeriv (f : E → F) (f' : E → E →L[ℝ] F) (μ : Measure E) : Prop :=
  HasWeakFDerivOn f f' .univ μ

variable {f g : E → F} {f' g' : E → E →L[ℝ] F} {s s' : Set E} {μ μ' : Measure E}
namespace HasWeakFDerivOn


lemma mono (h : HasWeakFDerivOn f f' s' μ) (hs : s ⊆ s') : HasWeakFDerivOn f f' s μ where
  locallyIntegrable := h.locallyIntegrable.mono_set hs
  locallyIntegrable_deriv := h.locallyIntegrable_deriv.mono_set hs
  integral_eq ϕ hϕ h2ϕ h3ϕ := h.integral_eq ϕ hϕ h2ϕ <| h3ϕ.trans <| interior_mono hs

lemma add (hf : HasWeakFDerivOn f f' s' μ) (hg : HasWeakFDerivOn g g' s' μ) :
    HasWeakFDerivOn (f + g) (f' + g') s' μ where
  locallyIntegrable := hf.locallyIntegrable.add hg.locallyIntegrable
  locallyIntegrable_deriv := hf.locallyIntegrable_deriv.add hg.locallyIntegrable_deriv
  integral_eq ϕ hϕ h2ϕ h3ϕ := by
    simp_rw [Pi.add_apply, smul_add, map_add]
    rw [integral_add, integral_add, neg_add, hf.integral_eq ϕ hϕ h2ϕ h3ϕ,
      hg.integral_eq ϕ hϕ h2ϕ h3ϕ]
    all_goals sorry



end
