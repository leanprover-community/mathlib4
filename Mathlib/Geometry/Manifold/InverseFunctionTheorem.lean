/-
Copyright (c) 2026 Matthew Spillman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Spillman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Inverse function theorem for manifolds

In this file, we derive the inverse function theorem for manifolds from the the inverse function
theorem for normed vector spaces (`ContDiffAt.toOpenPartialHomeomorph` XXX TODO!).

## Main definitions and results
* `extChartAtPartialDiffeomorph n hp`: we can restrict `extChartAt I p` to a `PartialDiffeomorph`
  between the manifold and its model vector space if `p` is an interior point.
* `ContDiffOn.toPartialDiffeomorph` : a stronger version of `ContDiffAt.toOpenPartialHomeomorph`,
  currently stated somewhat unnaturally by viewing the normed vector spaces as trivial manifolds
  (since there is not a normed vector space version of `PartialDiffeomorph`)
* `isLocalDiffeomorphAt_of_isInvertible_mfderiv`: if `f` is `C^n` on an open set `U` and has
  bijective differential at an interior point `p ∈ U`, then `f` is a local diffeomorphism at `p`.
  This holds for any `n ≥ 1` if we work over real or complex manifolds, and if `n = ω`
  (i.e., for analytic maps between analytic manifolds) over arbitrary fields.

## TODO
* restate `ContDiffOn.toPartialDiffeomorph` using a normed vector space version of
  `PartialDiffeomorph` (and add API to translate between the two types of `PartialDiffeomorph`)
* prove the manifold inverse function theorem (with adjustments where needed)
  when `p` is a boundary point and `f` preserves the boundary near `p`

## Tags

local diffeomorphism, manifold, inverse function theorem

-/

open Manifold Set
open scoped Topology

section DiffeoExtChartAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞} [IsManifold I n M] {p : M}

variable (I n p) in
/-- If `p` is an interior point of `M`, then `extChartAt I p` can be restricted to an open set
on which it becomes a `PartialDiffeomorph`.
-/
def extChartAtPartialDiffeomorph :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv := (extChartAt I p).restr ((extChartAt I p) ⁻¹' interior (range I))
  open_source := by
    rw [PartialEquiv.restr_source, extChartAt_source]
    exact isOpen_extChartAt_preimage _ isOpen_interior
  open_target := by
    rw [PartialEquiv.restr_target, PartialEquiv.target_inter_inv_preimage_preimage,
      extChartAt_target, inter_assoc, inter_comm (range I) _, inter_eq_left.mpr interior_subset]
    exact ((chartAt H p).open_target.preimage I.continuous_invFun).inter isOpen_interior
  contMDiffOn_toFun := contMDiffOn_extChartAt.mono (by simp)
  contMDiffOn_invFun := (contMDiffOn_extChartAt_symm p).mono inter_subset_left

@[simp] lemma toFun_extChartAtPartialDiffeomorph :
  ⇑(extChartAtPartialDiffeomorph I n p) = extChartAt I p := rfl

variable (I n p) in
lemma eqOn_extChartAtPartialDiffeomorph_extChartAt :
    EqOn (extChartAtPartialDiffeomorph I n p) (extChartAt I p)
      (extChartAtPartialDiffeomorph I n p).source :=
  graphOn_inj.mp rfl

variable (I n p) in
lemma eqOn_extChartAtPartialDiffeomorph_symm_extChartAt_symm :
    EqOn (extChartAtPartialDiffeomorph I n p).symm (extChartAt I p).symm
      (extChartAtPartialDiffeomorph I n p).target :=
  graphOn_inj.mp rfl

variable (n) in
lemma mem_extChartAtPartialDiffeomorph_source (hp : I.IsInteriorPoint p) :
    p ∈ (extChartAtPartialDiffeomorph I n p).source :=
  ⟨mem_extChartAt_source p,
  (mem_of_subset_of_mem (subset_sUnion_of_mem (Classical.choose_spec hp).1))
    (Classical.choose_spec hp).2⟩

variable (n) in
lemma mem_extChartAtPartialDiffeomorph_target (hp : I.IsInteriorPoint p) :
    (extChartAtPartialDiffeomorph I n p) p ∈ (extChartAtPartialDiffeomorph I n p).target :=
  (extChartAtPartialDiffeomorph I n p).map_source' (mem_extChartAtPartialDiffeomorph_source n hp)

lemma extChartAtPartialDiffeomorph_source_subset :
    (extChartAtPartialDiffeomorph I n p).source ⊆ (extChartAt I p).source  := by
  simp [extChartAtPartialDiffeomorph]

end DiffeoExtChartAt

@[expose] public section ManifoldInverseFunctionTheorem

open scoped ContDiff

section aux

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {n : ℕ∞ω} {f : E₁ → E₂} {f' : E₁ ≃L[𝕜] E₂} {p : E₁}

-- TODO: move to appropriate place; is there a better name?
-- TODO: mention the other version in each other's doc-strings
/-- This version does not assume we're working over `ℝ` or `ℂ`. -/
lemma ContDiffAt.hasStrictFDerivAt'' (hf : ContDiffAt 𝕜 n f p)
    (hf' : HasFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : minSmoothness 𝕜 1 ≤ n) :
    HasStrictFDerivAt f f'.toContinuousLinearMap p := by
  by_cases! h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜:= h.rclike
    rw [minSmoothness_of_isRCLikeNormedField] at hn
    have : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn
    sorry -- convert hf.hasStrictDerivAt (ENat.one_le_iff_ne_zero_withTop.mp hn) fails
  · rw [eq_top_of_minSmoothness_le_of_not_isRCLikeNormedField h hn] at hf
    rw [← hf'.fderiv]
    exact hf.analyticAt.hasStrictFDerivAt

end aux

namespace ContDiffOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {n : WithTop ℕ∞} {f : E₁ → E₂} {f' : E₁ ≃L[𝕜] E₂} {p : E₁} {U : Set E₁}
  (hf : ContDiffOn 𝕜 n f U) (hU : IsOpen U) (hpU : p ∈ U)

/-- If `f` is `C^n` on an open set `U` and has invertible strict derivative at `p ∈ U`, then it is a
local diffeomorphism near `p`. This is a stronger version of `ContDiffAt.toOpenPartialHomeomorph`
with a slightly stronger differentiability hypothesis.

This definition would ideally be located with the calculus API and not be stated in manifold terms,
but there is not currently a normed vector space version of `PartialDiffeomorph`.
-/
noncomputable def toPartialDiffeomorph
    (hf' : HasStrictFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : 1 ≤ n) :
  PartialDiffeomorph 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) E₁ E₂ n := by
  have U_nhd : U ∈ 𝓝 p := hU.mem_nhds hpU
  -- define `V ⊆ E₁`, the open set where `g'` is a continuous linear equivalence
  let V := (fderiv 𝕜 f) ⁻¹' (range ContinuousLinearEquiv.toContinuousLinearMap)
  have hUV: IsOpen (U ∩ V) :=
    (hf.continuousOn_fderiv_of_isOpen hU hn).isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  /- obtain an `OpenPartialHomeomorph E → F` using the standard inverse function theorem. We must
  restrict to `U ∩ V` so that we can later show ContDiff of the forward and inverse function -/
  let homeo := hf'.toOpenPartialHomeomorph.restrOpen _ hUV
  have homeo_contdiff : ContDiffOn 𝕜 n homeo.toFun homeo.source := by
    intro x hx
    have : homeo.source ⊆ U := subset_trans inter_subset_right inter_subset_left
    exact (hf.contDiffWithinAt (this hx)).mono this
  -- upgrade to a `PartialDiffeomorph` using `OpenPartialHomeomorph.contDiffAt_symm`
  exact {
    toPartialEquiv := homeo.toPartialEquiv
    open_source := homeo.open_source
    open_target := homeo.open_target
    contMDiffOn_toFun := by
      intro x hx
      refine ⟨homeo.continuousOn_toFun.continuousWithinAt hx, ?_⟩
      suffices ContDiffWithinAt 𝕜 n homeo homeo.source x by simpa [ContDiffWithinAtProp]
      exact homeo_contdiff x hx
    contMDiffOn_invFun := by
      intro y hy
      refine ⟨homeo.continuousOn_invFun.continuousWithinAt hy, ?_⟩
      rcases (subset_trans inter_subset_right inter_subset_right) (homeo.map_target hy) with
        ⟨g', hg'⟩
      have source_nhd : homeo.source ∈ 𝓝 (homeo.symm y) :=
        mem_nhds_iff.mpr ⟨homeo.source, subset_refl _, homeo.open_source, homeo.map_target hy⟩
      have : DifferentiableAt 𝕜 homeo (homeo.symm y) := (homeo_contdiff.differentiableOn
        (ENat.one_le_iff_ne_zero_withTop.mp hn)
        (homeo.symm y) (homeo.map_target hy)).differentiableAt source_nhd
      exact (homeo.contDiffAt_symm hy (hg' ▸ this.hasFDerivAt)
        (homeo_contdiff.contDiffAt source_nhd)).contDiffWithinAt
  }

@[simp] lemma toFun_toPartialDiffeomorph
    (hf' : HasStrictFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : 1 ≤ n) :
    ⇑(hf.toPartialDiffeomorph hU hpU hf' hn) = f := by
  rfl

lemma toPartialDiffeomorph_mem_source
    (hf' : HasStrictFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : 1 ≤ n) :
    p ∈ (hf.toPartialDiffeomorph hU hpU hf' hn).source :=
  ⟨hf'.mem_toOpenPartialHomeomorph_source, hpU, f', Eq.symm (hf'.hasFDerivAt.fderiv)⟩

/-- If `f` is `C^n` on an open set `U` and has invertible derivative at `p ∈ U`, then it is a
local diffeomorphism near `p`. This is a stronger version of `ContDiffAt.toOpenPartialHomeomorph`
with a slightly stronger differentiability hypothesis.

This definition would ideally be located with the calculus API and not be stated in manifold terms,
but there is not currently a normed vector space version of `PartialDiffeomorph`.
-/
noncomputable def toPartialDiffeomorph'
    (hf' : HasFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : minSmoothness 𝕜 1 ≤ n) :
    PartialDiffeomorph 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) E₁ E₂ n :=
  hf.toPartialDiffeomorph hU hpU ((hf.contDiffAt (hU.mem_nhds hpU)).hasStrictFDerivAt'' hf' hn)
    (le_minSmoothness.trans hn)

@[simp] lemma toFun_toPartialDiffeomorph'
    (hf' : HasFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : minSmoothness 𝕜 1 ≤ n) :
    ⇑(hf.toPartialDiffeomorph' hU hpU hf' hn) = f := by
  rfl

lemma toPartialDiffeomorph'_mem_source
    (hf' : HasFDerivAt f (f' : E₁ →L[𝕜] E₂) p) (hn : minSmoothness 𝕜 1 ≤ n) :
    p ∈ (hf.toPartialDiffeomorph' hU hpU hf' hn).source :=
  letI hf := hf.contDiffAt (hU.mem_nhds hpU)
  ⟨(hf.hasStrictFDerivAt'' hf' hn).mem_toOpenPartialHomeomorph_source, hpU, f', hf'.fderiv.symm⟩

end ContDiffOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {n : WithTop ℕ∞} [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]

/-- The **inverse function theorem** for manifolds, at an interior point.
If `f` is `C^n` on a neighborhood of an interior point `p` and has invertible differential at `p`,
then `f` is a local diffeomorphism at `p`. -/
theorem isLocalDiffeomorphAt_of_isInvertible_mfderiv {p : M₁} (hp : I₁.IsInteriorPoint p)
    {A : Set M₁} (hA : IsOpen A) (hpA : p ∈ A) {f : M₁ → M₂} (hf : ContMDiffOn I₁ I₂ n f A)
    (hf' : ContinuousLinearMap.IsInvertible (mfderiv% f p)) (hn : minSmoothness 𝕜 1 ≤ n) :
    IsLocalDiffeomorphAt I₁ I₂ n f p := by
  -- Since `p` is an interior point, also `f p` is an interior point (of `M₂`).
  have mDiffAt_f_p : MDiffAt f p := (hf.contMDiffAt (hA.mem_nhds hpA)).mdifferentiableAt
    (by rw [← ENat.one_le_iff_ne_zero_withTop]; exact le_minSmoothness.trans hn)
  have hfp : I₂.IsInteriorPoint (f p) :=
    mDiffAt_f_p.isInteriorPoint_of_surjective_mfderiv hf'.surjective hp
  -- Consider the coordinate representation `g` of f in local charts at `p` and `f p`.
  let g : E₁ → E₂ := writtenInExtChartAt I₁ I₂ p f
  let φ₁ : PartialDiffeomorph I₁ 𝓘(𝕜, E₁) M₁ E₁ n := extChartAtPartialDiffeomorph I₁ n p
  let ψ₁ : PartialDiffeomorph I₂ 𝓘(𝕜, E₂) M₂ E₂ n := extChartAtPartialDiffeomorph I₂ n (f p)
  -- Show that `g` is `C^n` on some open set containing `extChartAt I₁ p p`.
  let U : Set E₁ := φ₁ '' (φ₁.source ∩ (A ∩ f ⁻¹' ψ₁.source))
  have hg : ContDiffOn 𝕜 n g U := by
    refine ((contMDiffOn_iff.mp hf).2 p (f p)).mono ?_
    rintro e ⟨m, ⟨hm₁, hm₂, hm₃⟩, rfl⟩
    refine ⟨inter_subset_left (φ₁.map_source hm₁), ?_⟩
    replace hm₁ : m ∈ (chartAt H₁ p).source := by
      grw [extChartAtPartialDiffeomorph_source_subset] at hm₁
      simpa using hm₁
    replace hm₃ : f m ∈ (chartAt H₂ (f p)).source := by
      grw [extChartAtPartialDiffeomorph_source_subset] at hm₃
      simpa using hm₃
    simp_all [φ₁, (chartAt H₁ p).left_inv hm₁]
  have U_open : IsOpen U := by
    refine φ₁.toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ inter_subset_left
    exact φ₁.open_source.inter (hf.continuousOn.isOpen_inter_preimage hA ψ₁.open_source)
  have hp' : extChartAt I₁ p p ∈ U :=
    mem_image_of_mem _ ⟨mem_extChartAtPartialDiffeomorph_source n hp,
      hpA, mem_extChartAtPartialDiffeomorph_source n hfp⟩
  -- Use `hf'` to show that the derivative of `g` at `φ₀ p` is a continuous linear equivalence.
  obtain ⟨g', hg'⟩ := isInvertible_fderivWithin_writtenInExtChartAt hf'
  have hg' : HasFDerivAt g g'.toContinuousLinearMap (extChartAt I₁ p p) :=
    hg' ▸ mDiffAt_f_p.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt.hasFDerivAt
      (range_mem_nhds_isInteriorPoint hp)
  replace hg' := ContDiffAt.hasStrictFDerivAt'' (hg.contDiffAt (U_open.mem_nhds hp')) hg' hn
  /- Apply the inverse function theorem in normed spaces: obtain a local inverse for `g`.
  Compose with the charts to obtain the desired partial diffeomorphism `M₁ → M₂`. -/
  use (φ₁.trans (hg.toPartialDiffeomorph U_open hp' hg' (le_minSmoothness.trans hn))).trans ψ₁.symm
  constructor
  · refine ⟨⟨mem_extChartAtPartialDiffeomorph_source n hp,
      (hg.toPartialDiffeomorph_mem_source U_open hp' hg' (le_minSmoothness.trans hn))⟩, ?_⟩
    simpa [φ₁, ψ₁, g] using mem_extChartAtPartialDiffeomorph_target n hfp
  · rintro m ⟨⟨hm₁, _, hm₂, _⟩, _⟩
    have hm := extChartAtPartialDiffeomorph_source_subset (n := n) hm₁
    have hfm := extChartAtPartialDiffeomorph_source_subset (n := n)
      (φ₁.injOn.mem_of_mem_image inter_subset_left hm₁ hm₂).2.2
    exact (extChartAt_symm_writtenInExtChartAt_extChartAt hm hfm).symm

end ManifoldInverseFunctionTheorem
