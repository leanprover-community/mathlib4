/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
-- import Mathlib.Analysis.Calculus.FDeriv.Basic
-- import Mathlib.MeasureTheory.Function.LocallyIntegrable
-- import Mathlib.MeasureTheory.Integral.
import Mathlib

/-!
# Weak Derivatives


## Tags

weak derivative

-/

open Filter Asymptotics ContinuousLinearMap Set Metric MeasureTheory Function

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

namespace MeasureTheory

section LocallyIntegrable

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}
  [OpensMeasurableSpace X] [NormedAddCommGroup E] {f : X → E} {s t : Set X}

theorem LocallyIntegrableOn.union_support_compl (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn f (s ∪ (tsupport f)ᶜ) μ := by
  sorry

theorem LocallyIntegrableOn.locallyIntegrable (hf : LocallyIntegrableOn f s μ)
    (h2f : tsupport f ⊆ s) :
    LocallyIntegrable f μ := by
  rw [← locallyIntegrableOn_univ]
  convert hf.union_support_compl
  rw [eq_comm, eq_univ_iff_forall]
  tauto

-- theorem LocallyIntegrableOn.IntegrableOn (hf : HasCompactSupport f) :
--     LocallyIntegrableOn f s μ ↔ IntegrableOn f s μ := by
--   refine ⟨fun h2 ↦ ?_, fun h ↦ h.locallyIntegrableOn⟩
--   sorry

theorem LocallyIntegrableOn.integrable_of_continuousOn_smul
    [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedField 𝕜]
    [SecondCountableTopologyEither X 𝕜] [NormedSpace 𝕜 E] {f : X → E} {g : X → 𝕜} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : Continuous g)
    (h2g : HasCompactSupport g) (h3g : support g ⊆ s) :
    Integrable (fun x => g x • f x) μ := by
  have : LocallyIntegrableOn (fun x ↦ g x • f x) s μ := hf.continuousOn_smul hs hg.continuousOn
  have : LocallyIntegrable (fun x ↦ g x • f x) μ := sorry
  sorry





end LocallyIntegrable

end MeasureTheory

-- variable {ℝ : Type*} [RCLike ℝ] -- maybe make ℝ?
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {G' : Type*} [NormedAddCommGroup G'] [InnerProductSpace ℝ G']
variable {f g : E → F} {f' g' : E → E →L[ℝ] F} {s s' : Set E} {μ μ' : Measure E}


/-! ## Preliminaries -/

protected theorem MeasureTheory.LocallyIntegrableOn.smul
    (hf : LocallyIntegrableOn f s μ) (c : ℝ) : LocallyIntegrableOn (c • f) s μ :=
  fun x hx ↦ (hf x hx).smul c

protected theorem DifferentiableOn.ofHasFDerivWithinAt
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : DifferentiableOn ℝ /-𝕜-/ f s :=
  fun x hx ↦ (hf x hx).differentiableWithinAt

open InnerProductSpace
theorem integral_fderiv_eq_zero''' {f : E × ℝ → F} (μ : Measure E) [SFinite μ]
    (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) :
    ∫ x, fderiv ℝ f x (0, 1) ∂(μ.prod volume) = 0 := by
  have : ∫ x, fderiv ℝ (f ∘ Prod.mk x.1) x.2 1 ∂(μ.prod volume) = 0
  · rw [integral_prod]
    dsimp
    rw [← integral_zero]
    congr! with _ x
    simp
    rw [integral_eq_zero_of_hasDerivAt_of_integrable]
    intro x
    apply DifferentiableAt.hasDerivAt
    sorry --convert (hf.comp <| contDiff_prod_mk_left x).differentiable le_rfl |>.differentiableAt
    -- exact (fun x ↦ hasDerivAt_fderiv)
    all_goals sorry
  convert this with x
  rw [fderiv.comp]
  simp
  all_goals sorry



theorem integral_fderiv_eq_zero'' {ι} [Fintype ι] (f : EuclideanSpace ℝ ι → F)
    (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) :
    ∫ x, fderiv ℝ f x = 0 := by
  rw [← ContinuousLinearMap.coe_inj]
  refine (EuclideanSpace.basisFun ι ℝ).toBasis.ext (fun i ↦ ?_)
  dsimp only [coe_coe, ContinuousLinearMap.coe_zero, LinearMap.zero_apply]
  rw [integral_apply]
  all_goals sorry

theorem integral_fderiv_eq_zero' [MeasurableSpace G'] [BorelSpace G'] [FiniteDimensional ℝ G']
    {f : G' → F} (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) :
    ∫ x, fderiv ℝ f x = 0 := by
  ext v
  rw [integral_apply, zero_apply]
  all_goals sorry

-- maybe inner product space
theorem integral_fderiv_eq_zero [FiniteDimensional ℝ E] (f : E → F)
    (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) (μ : Measure E) :
    ∫ x, fderiv ℝ f x ∂μ = 0 := by sorry
--   rw [← ContinuousLinearMap.coe_inj]
--   refine Basis.ext _ (fun i ↦ ?_)
--   rw [integral_apply, zero_apply]

-- /-- Special case of the divergence theorem for compactly supported vector fields. -/
-- theorem integral_fderiv_eq_zero (f : E → E)
--     (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) (μ : Measure E) :
--     ∫ x, LinearMap.trace ℝ E (fderiv ℝ f x) ∂μ = 0 :=
--   sorry


-- MeasureTheory.LocallyIntegrableOn.continuousOn_smul

/-! ## Weak derivatives -/

/-- A function `f` has the continuous linear map `f'` as derivative weak derivative ... -/
-- should we replace `interior s` by `s`, and just assume `IsOpen s` when needed?
structure HasWeakFDerivOn (f : E → F) (f' : E → E →L[ℝ] F) (s : Set E) (μ : Measure E) : Prop where
  locallyIntegrable : LocallyIntegrableOn f (interior s) μ
  locallyIntegrable_deriv : LocallyIntegrableOn f' (interior s) μ
  integral_eq : ∀ (ϕ : E → ℝ), ContDiff ℝ ⊤ ϕ → HasCompactSupport ϕ →
    Function.support ϕ ⊆ interior s →
    ∫ x, ϕ x • f' x ∂μ = - ∫ x, smulRightL ℝ E F (fderiv ℝ ϕ x) (f x) ∂μ

@[fun_prop]
def HasWeakFDeriv (f : E → F) (f' : E → E →L[ℝ] F) (μ : Measure E) : Prop :=
  HasWeakFDerivOn f f' .univ μ

namespace HasWeakFDerivOn

lemma mono (h : HasWeakFDerivOn f f' s' μ) (hs : s ⊆ s') : HasWeakFDerivOn f f' s μ where
  locallyIntegrable := h.locallyIntegrable.mono_set <| interior_mono hs
  locallyIntegrable_deriv := h.locallyIntegrable_deriv.mono_set <| interior_mono hs
  integral_eq ϕ hϕ h2ϕ h3ϕ := h.integral_eq ϕ hϕ h2ϕ <| h3ϕ.trans <| interior_mono hs

lemma add [OpensMeasurableSpace E] [LocallyCompactSpace E] [SecondCountableTopologyEither E F]
    [IsLocallyFiniteMeasure μ]
    (hf : HasWeakFDerivOn f f' s μ) (hg : HasWeakFDerivOn g g' s μ) :
    HasWeakFDerivOn (f + g) (f' + g') s μ where
  locallyIntegrable := hf.locallyIntegrable.add hg.locallyIntegrable
  locallyIntegrable_deriv := hf.locallyIntegrable_deriv.add hg.locallyIntegrable_deriv
  integral_eq ϕ hϕ h2ϕ h3ϕ := by
    simp_rw [Pi.add_apply, smul_add, map_add]
    rw [integral_add, integral_add, neg_add, hf.integral_eq ϕ hϕ h2ϕ h3ϕ,
      hg.integral_eq ϕ hϕ h2ϕ h3ϕ]
    sorry
    sorry
    -- have := hf.locallyIntegrable_deriv.integrable_smul_left_of_hasCompactSupport
    --   isOpen_interior hϕ.continuous.continuousOn

    all_goals sorry

lemma smul (hf : HasWeakFDerivOn f f' s μ) (c : ℝ) :
    HasWeakFDerivOn (c • f) (c • f') s μ where
  locallyIntegrable := hf.locallyIntegrable.smul c
  locallyIntegrable_deriv := hf.locallyIntegrable_deriv.smul c
  integral_eq ϕ hϕ h2ϕ h3ϕ := by
    simp only [Pi.smul_apply, LinearMapClass.map_smul, smul_comm _ c]
    rw [integral_smul, integral_smul, ← smul_neg, hf.integral_eq ϕ hϕ h2ϕ h3ϕ]

lemma ofHasFDerivAt
    [OpensMeasurableSpace E] [SecondCountableTopology E] [IsLocallyFiniteMeasure μ]
    [FiniteDimensional ℝ E]
    -- [MeasurableSpace G'] [BorelSpace G'] [FiniteDimensional ℝ G']
    (hf : ∀ x ∈ interior s, HasFDerivWithinAt f (f' x) (interior s) x)
    (hf' : ContinuousOn f' (interior s)) (c : ℝ) :
    HasWeakFDerivOn f f' s μ where
  locallyIntegrable := by
    have : DifferentiableOn ℝ f (interior s) := .ofHasFDerivWithinAt hf
    exact this.continuousOn.locallyIntegrableOn isOpen_interior.measurableSet
  locallyIntegrable_deriv := hf'.locallyIntegrableOn isOpen_interior.measurableSet
  integral_eq ϕ hϕ h2ϕ h3ϕ := by
    rw [eq_neg_iff_add_eq_zero]
    suffices : ∫ x, fderiv ℝ (fun x ↦ ϕ x • f x) x ∂μ = 0
    · rw [← this, ← integral_add]
      congr! with x
      by_cases hx : x ∈ interior s; swap
      · sorry
      rw [fderiv_smul]
      all_goals sorry
    rw [integral_fderiv_eq_zero]
    all_goals sorry

#check integral_add




end HasWeakFDerivOn

end
