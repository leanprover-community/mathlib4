/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Weak Derivatives


## Tags

weak derivative

-/

open Filter Asymptotics ContinuousLinearMap Set Metric MeasureTheory Function

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

attribute [simp] Filter.EventuallyEq.rfl

namespace MeasureTheory

section LocallyIntegrable

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [MeasurableSpace E'] [NormedSpace 𝕜 E']
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
-- variable [OpensMeasurableSpace E] [OpensMeasurableSpace E'] -- or Borel?
variable {f : X → E} {s t : Set X}

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


theorem LocallyIntegrableOn.integrable_of_continuousOn_clm (L : E' →L[𝕜] E →L[𝕜] F)
    {f : X → E} {g : X → E'} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : Continuous g)
    (h2g : HasCompactSupport g) (h3g : tsupport g ⊆ s) :
    Integrable (fun x => L (g x) (f x)) μ := by
  have : LocallyIntegrableOn (fun x ↦ L (g x) (f x)) s μ := sorry
  -- hf.continuousOn_smul hs hg.continuousOn
  have : LocallyIntegrable (fun x ↦ L (g x) (f x)) μ := sorry
  sorry

theorem LocallyIntegrableOn.integrable_of_continuousOn_smul
    {f : X → E} {g : X → 𝕜} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : Continuous g)
    (h2g : HasCompactSupport g) (h3g : tsupport g ⊆ s) :
    Integrable (fun x => g x • f x) μ :=
  hf.integrable_of_continuousOn_clm (.lsmul 𝕜 𝕜) hs hg h2g h3g

theorem LocallyIntegrableOn.integrable_of_continuousOn_smulRight
    {f : X → E} {g : X → E' →L[𝕜] 𝕜} {s : Set X}
    (hs : IsOpen s) (hf : LocallyIntegrableOn f s μ) (hg : Continuous g)
    (h2g : HasCompactSupport g) (h3g : tsupport g ⊆ s) :
    Integrable (fun x => (g x).smulRight (f x)) μ :=
  hf.integrable_of_continuousOn_clm (.smulRightL 𝕜 E' E) hs hg h2g h3g

theorem ContDiffAt.clm_apply {n : ℕ∞} {f : E → F →L[𝕜] G} {g : E → F} {x : E}
    (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x (g x)) x :=
  isBoundedBilinearMap_apply.contDiff.contDiffAt.comp x <| hf.prod hg

theorem ContDiffOn_iff_of_mem_nhdsSet {n : ℕ∞} {f : E → F} {s : Set E}
    (hs : s ∈ 𝓝ˢ (tsupport f)) :
    ContDiffOn 𝕜 n f s ↔ ContDiff 𝕜 n f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contDiffOn⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h x (subset_of_mem_nhdsSet hs hx) |>.contDiffAt <| nhds_le_nhdsSet hx hs
  · rw [not_mem_tsupport_iff_eventuallyEq] at hx
    exact contDiffAt_const.congr_of_eventuallyEq hx

theorem ContDiff.clm_apply₂_of_mem_nhdsSet (L : F →L[𝕜] F' →L[𝕜] G)
    {n : ℕ∞} {f : E → F} {g : E → F'} {s t : Set E}
    (hf : ContDiffOn 𝕜 n f t)
    (hg : ContDiffOn 𝕜 n g s)
    (hs : s ∈ 𝓝ˢ (tsupport f)) (ht : t ∈ 𝓝ˢ (tsupport g))  :
    ContDiff 𝕜 n (fun x => L (f x) (g x)) := by
  have : s ∩ t ∈ 𝓝ˢ (tsupport (fun x ↦ L (f x) (g x))) := by
    refine nhdsSet_mono ?_ <|
      inter_mem (nhdsSet_mono inter_subset_left hs) (nhdsSet_mono inter_subset_right ht)
    refine subset_inter (closure_mono ?_) (closure_mono ?_) <;>
      simp (config := {contextual := true}) [-support_subset_iff, support_subset_iff']
  rw [← ContDiffOn_iff_of_mem_nhdsSet this]
  refine ContDiffOn.clm_apply (contDiffOn_const.clm_apply <| hf.mono inter_subset_right) <|
    hg.mono inter_subset_left

end LocallyIntegrable

end MeasureTheory

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
theorem smulRightL_apply (c : E →L[𝕜] 𝕜) (f : F) : smulRightL 𝕜 E F c f = smulRight c f :=
  rfl

@[simp]
theorem fderiv_zero : fderiv 𝕜 (0 : E → F) = 0 := fderiv_const 0

theorem fderiv_zero_apply {x : E} : fderiv 𝕜 (0 : E → F) x = 0 := fderiv_const_apply 0

end NormedSpace

-- section NormedField
-- variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] {μ : Measure X}
-- variable {𝕜 : Type*} [NormedField 𝕜]
-- variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace 𝕜 E]
-- variable {E' : Type*} [NormedAddCommGroup E'] [MeasurableSpace E'] [NormedSpace 𝕜 E']
-- variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
-- variable [OpensMeasurableSpace E] [OpensMeasurableSpace E'] -- or Borel?


-- end NormedField

-- variable {ℝ : Type*} [RCLike ℝ] -- maybe make ℝ?
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {G' : Type*} [NormedAddCommGroup G'] [InnerProductSpace ℝ G']
variable {f g : E → F} {f' g' : E → E →L[ℝ] F} {s s' : Set E} {μ μ' : Measure E}


/-! ## Preliminaries -/

protected theorem MeasureTheory.LocallyIntegrableOn.smul
    (hf : LocallyIntegrableOn f s μ) (c : ℝ) : LocallyIntegrableOn (c • f) s μ :=
  fun x hx ↦ hf x hx |>.smul c

protected theorem DifferentiableOn.ofHasFDerivWithinAt
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : DifferentiableOn ℝ /-𝕜-/ f s :=
  fun x hx ↦ hf x hx |>.differentiableWithinAt

protected theorem DifferentiableOn.ofHasFDerivAt
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x) : DifferentiableOn ℝ /-𝕜-/ f s :=
  fun x hx ↦ hf x hx |>.differentiableAt.differentiableWithinAt


open InnerProductSpace
theorem integral_fderiv_eq_zero''' {f : E × ℝ → F} (μ : Measure E) [SFinite μ]
    (hf : ContDiff ℝ 1 f) (h2f : HasCompactSupport f) :
    ∫ x, fderiv ℝ f x (0, 1) ∂(μ.prod volume) = 0 := by
  have : ∫ x, fderiv ℝ (f ∘ Prod.mk x.1) x.2 1 ∂(μ.prod volume) = 0 := by
    rw [integral_prod]
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
-- does the derivative have to be continuous?
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
  integral_eq' : ∀ (ϕ : E → ℝ), ContDiff ℝ ⊤ ϕ → HasCompactSupport ϕ →
    tsupport ϕ ⊆ interior s →
    ∫ x, ϕ x • f' x ∂μ = - ∫ x, smulRight (fderiv ℝ ϕ x) (f x) ∂μ

@[fun_prop]
def HasWeakFDeriv (f : E → F) (f' : E → E →L[ℝ] F) (μ : Measure E) : Prop :=
  HasWeakFDerivOn f f' .univ μ

namespace HasWeakFDerivOn

lemma mono (h : HasWeakFDerivOn f f' s' μ) (hs : s ⊆ s') : HasWeakFDerivOn f f' s μ where
  locallyIntegrable := h.locallyIntegrable.mono_set <| interior_mono hs
  locallyIntegrable_deriv := h.locallyIntegrable_deriv.mono_set <| interior_mono hs
  integral_eq' ϕ hϕ h2ϕ h3ϕ := h.integral_eq' ϕ hϕ h2ϕ <| h3ϕ.trans <| interior_mono hs

lemma add [OpensMeasurableSpace E] [LocallyCompactSpace E] [SecondCountableTopologyEither E F]
    [IsLocallyFiniteMeasure μ]
    (hf : HasWeakFDerivOn f f' s μ) (hg : HasWeakFDerivOn g g' s μ) :
    HasWeakFDerivOn (f + g) (f' + g') s μ where
  locallyIntegrable := hf.locallyIntegrable.add hg.locallyIntegrable
  locallyIntegrable_deriv := hf.locallyIntegrable_deriv.add hg.locallyIntegrable_deriv
  integral_eq' ϕ hϕ h2ϕ h3ϕ := by
    simp_rw [Pi.add_apply, smul_add, ← smulRightL_apply, map_add]
    rw [integral_add, integral_add, neg_add, hf.integral_eq' ϕ hϕ h2ϕ h3ϕ,
      hg.integral_eq' ϕ hϕ h2ϕ h3ϕ]
    sorry
    sorry
    -- have := hf.locallyIntegrable_deriv.integrable_smul_left_of_hasCompactSupport
    --   isOpen_interior hϕ.continuous.continuousOn

    all_goals sorry

lemma smul (hf : HasWeakFDerivOn f f' s μ) (c : ℝ) :
    HasWeakFDerivOn (c • f) (c • f') s μ where
  locallyIntegrable := hf.locallyIntegrable.smul c
  locallyIntegrable_deriv := hf.locallyIntegrable_deriv.smul c
  integral_eq' ϕ hϕ h2ϕ h3ϕ := by
    simp_rw [← smulRightL_apply, Pi.smul_apply, LinearMapClass.map_smul, smul_comm _ c,
      integral_smul, ← smul_neg, hf.integral_eq' ϕ hϕ h2ϕ h3ϕ, smulRightL_apply]

lemma ofHasFDerivAt
    [OpensMeasurableSpace E] [SecondCountableTopology E] [IsLocallyFiniteMeasure μ]
    [FiniteDimensional ℝ E]
    -- [MeasurableSpace G'] [BorelSpace G'] [FiniteDimensional ℝ G']
    (hf : ∀ x ∈ interior s, HasFDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (interior s)) (c : ℝ) : HasWeakFDerivOn f f' s μ := by
  have h0f : LocallyIntegrableOn f (interior s) μ := by
    have : DifferentiableOn ℝ f (interior s) := .ofHasFDerivAt hf
    exact this.continuousOn.locallyIntegrableOn isOpen_interior.measurableSet
  have h0f' : LocallyIntegrableOn f' (interior s) μ :=
    hf'.locallyIntegrableOn isOpen_interior.measurableSet
  exact
  { locallyIntegrable := h0f
    locallyIntegrable_deriv := h0f'
    integral_eq' := by
      intro ϕ hϕ h2ϕ h3ϕ
      rw [eq_neg_iff_add_eq_zero]
      suffices ∫ x, fderiv ℝ (fun x ↦ ϕ x • f x) x ∂μ = 0 by
        rw [← this, ← integral_add]
        congr! with x
        by_cases hx : x ∈ interior s; swap
        · have h1 : ϕ =ᶠ[𝓝 x] 0 := by
            rw [← not_mem_tsupport_iff_eventuallyEq]
            exact fun a ↦ hx (h3ϕ a)
          have h2 : fderiv ℝ ϕ x = 0 := by
            rw [h1.fderiv_eq, fderiv_zero_apply]
          have h3 : fderiv ℝ (fun x ↦ ϕ x • f x) x = 0 := by
            rw [← fderiv_zero_apply (x := x)]
            apply Filter.EventuallyEq.fderiv_eq
            calc (fun x ↦ ϕ x • f x) =ᶠ[𝓝 x] (fun x ↦ (0 : E → ℝ) x • f x) := h1.smul .rfl
              _ =ᶠ[𝓝 x] (fun x ↦ 0) := by simp
          simp [← smulRightL_apply, h1.self_of_nhds, h2, h3]
        rw [fderiv_smul (hϕ.contDiffAt.differentiableAt le_top) (hf x hx).differentiableAt,
          hf x hx |>.fderiv]
        exact h0f'.integrable_of_continuousOn_smul isOpen_interior hϕ.continuous h2ϕ h3ϕ
        exact h0f.integrable_of_continuousOn_smulRight isOpen_interior
          (hϕ.continuous_fderiv le_top) (h2ϕ.fderiv ℝ) ((tsupport_fderiv_subset ℝ).trans h3ϕ)
      rw [integral_fderiv_eq_zero]
      refine ContDiff.clm_apply₂_of_mem_nhdsSet (lsmul ℝ ℝ)
        (hϕ.of_le le_top).contDiffOn ?_ (subset_interior_iff_mem_nhdsSet.mp h3ϕ) univ_mem

      all_goals sorry
    }






end HasWeakFDerivOn

end
-- #minimize_imports
