/-
Copyright (c) 2026 Matthew Spillman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Spillman
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Inverse function theorem for manifolds

In this file, we derive the inverse function theorem for manifolds from the the inverse function
theorem for normed vector spaces over an `RCLike` field (`ContDiffAt.toOpenPartialHomeomorph`).

## Main definitions
* `diffeoExtChartAt n hp`: we can restrict `extChartAt I p` to a `PartialDiffeomorph` between the
  manifold and its model vector space if `p` is an interior point.
* `ContDiffOn.toPartialDiffeomorph` : a stronger version of `ContDiffAt.toOpenPartialHomeomorph`,
  currently stated somewhat unnaturally by viewing the normed vector spaces as trivial manifolds
  (since there is not a normed vector space version of `PartialDiffeomorph`)

## Main results
* `isLocalDiffeomorphAt_of_bijective_mfderiv`: if `f` is `ContMDiffOn` an open set `U` and has
  bijective differential at an interior point `p ∈ U`, then `f` is a local diffeomorphism at `p`.

## TODO
* restate `ContDiffOn.toPartialDiffeomorph` using a normed vector space version of
  `PartialDiffeomorph` (and add API to translate between the two types of `PartialDiffeomorph`)
* prove the manifold inverse function theorem (with adjustments if needed) when `p` is a boundary
  point and `f` preserves the boundary near`p`

## Tags
local diffeomorphism, manifold, inverse function theorem

-/

open Manifold Set TopologicalSpace

section DiffeoExtChartAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞)

/-- If `p` is an interior point of `M`, then `extChartAt I p` can be restricted to an open set
on which it becomes a `PartialDiffeomorph` (viewing `E` as a manifold modeled on itself trivially)
-/
def diffeoExtChartAt [IsManifold I n M] {p : M} (hp : I.IsInteriorPoint p) :
    PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toPartialEquiv :=
    ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).toPartialEquiv
  open_source := ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).open_source
  open_target := ((chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)).open_target
  contMDiffOn_toFun := by
    set homeo := (chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)
    -- this is just the identity in coordinates
    have h₁: homeo.source ⊆ (chartAt H p).source := by simp [homeo]
    have h₂ : MapsTo homeo homeo.source (chartAt E (homeo p)).source := by simp [MapsTo]
    refine (contMDiffOn_iff_of_subset_source h₁ h₂).mpr ⟨homeo.continuousOn_toFun, ?_⟩
    set f := homeo ∘ (chartAt H p).symm ∘ I.symm
    set s := (fun a ↦ I ((chartAt H p) a)) '' homeo.source
    change ContDiffOn 𝕜 n f s
    have : ∀ e ∈ s, f e = e := by
      rintro e ⟨w, ⟨hw, _⟩, rfl⟩
      simp [f, homeo, openPartialHomeomorph_of_isInteriorPoint,
        (chartAt H p).right_inv ((chartAt H p).map_source hw)]
    exact contDiffOn_id.congr this
  contMDiffOn_invFun := by
    set homeo := (chartAt H p).trans (openPartialHomeomorph_of_isInteriorPoint hp)
    -- this is also just the identity in coordinates
    have h₁ : homeo.target ⊆ (chartAt E (homeo p)).source := by simp [homeo]
    have h₂ : MapsTo homeo.invFun homeo.target  (chartAt H p).source :=
      fun _ he ↦ (homeo.map_target he).1
    refine (contMDiffOn_iff_of_subset_source h₁ h₂).mpr ⟨homeo.continuousOn_invFun, ?_⟩
    set f := (↑I ∘ ↑(chartAt H p)) ∘ ↑homeo.symm
    suffices ContDiffOn 𝕜 n f homeo.target by simpa
    have : ∀ e ∈ homeo.target, f e = e := by
      intro e he
      simp [f, homeo, openPartialHomeomorph_of_isInteriorPoint] at he ⊢
      simp [(chartAt H p).right_inv he.2, I.right_inv he.1.1]
    exact contDiffOn_id.congr this

lemma eqOn_diffeoExtChartAt_extChartAt [IsManifold I n M] {p : M} (hp : I.IsInteriorPoint p) :
    EqOn (diffeoExtChartAt n hp) (extChartAt I p) (diffeoExtChartAt n hp).source :=
  graphOn_inj.mp rfl

lemma eqOn_diffeoExtChartAt_symm_extChartAt_symm [IsManifold I n M] {p : M}
    (hp : I.IsInteriorPoint p) :
    EqOn (diffeoExtChartAt n hp).symm (extChartAt I p).symm (diffeoExtChartAt n hp).target :=
  graphOn_inj.mp rfl

lemma mem_diffeoExtChartAt_source [IsManifold I n M] {p : M} (hp : I.IsInteriorPoint p) :
    p ∈ (diffeoExtChartAt n hp).source := ⟨mem_chart_source H p, (Classical.choose_spec hp).2⟩

lemma diffeoExtChartAt_source_subset [IsManifold I n M] {p : M} (hp : I.IsInteriorPoint p) :
    (diffeoExtChartAt n hp).source ⊆ (extChartAt I p).source  := by simp [diffeoExtChartAt]

lemma diffeoExtChartAt_target_subset [IsManifold I n M] {p : M} (hp : I.IsInteriorPoint p) :
    (diffeoExtChartAt n hp).target ⊆ (extChartAt I p).target  := by
  intro e he
  rw [← (diffeoExtChartAt n hp).image_source_eq_target] at he
  rcases he with ⟨m, hm, rfl⟩
  rw [← (extChartAt I p).image_source_eq_target]
  exact ⟨m, (diffeoExtChartAt_source_subset n hp) hm, eqOn_diffeoExtChartAt_extChartAt n hp hm⟩

end DiffeoExtChartAt

@[expose] public section ManifoldInverseFunctionTheorem

namespace ContDiffOn

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {n : WithTop ℕ∞} {f : E₁ → E₂} {f' : E₁ ≃L[𝕜] E₂} {p : E₁} {U : Set E₁}
  (hg : ContDiffOn 𝕜 n f U) (hU : IsOpen U) (hpU : p ∈ U) (hg' : HasFDerivAt f (f' : E₁ →L[𝕜] E₂) p)
  (hn : n ≠ 0)

/-- If `f` is `ContDiffOn` an open set `U` and has invertible derivative at `p ∈ U`, then it is a
local diffeomorphism near `p`. This is a stronger version of `ContDiffAt.toOpenPartialHomeomorph`
with a slightly stronger differentiability hypothesis.

This definition would ideally be located with the calculus API and not be stated in manifold terms,
but there is not currently a normed vector space version of `PartialDiffeomorph`.
-/
noncomputable def toPartialDiffeomorph : PartialDiffeomorph 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) E₁ E₂ n := by
  have U_nhd : U ∈ nhds p := hU.mem_nhds hpU
  -- define `V ⊆ E₁`, the open set where `g'` is a continuous linear equivalence
  set V := (fderiv 𝕜 f) ⁻¹' (range ContinuousLinearEquiv.toContinuousLinearMap)
  have hUV: IsOpen (U ∩ V) :=
    (hg.continuousOn_fderiv_of_isOpen hU (ENat.one_le_iff_ne_zero_withTop.mpr hn)
    ).isOpen_inter_preimage hU (ContinuousLinearEquiv.isOpen)
  /- obtain an `OpenPartialHomeomorph E → F` using the standard inverse function theorem. We must
  restrict to `U ∩ V` so that we can later show ContDiff of the forward and inverse function -/
  set homeo := ((hg.contDiffAt U_nhd).toOpenPartialHomeomorph f hg' hn).restrOpen _ hUV
  have homeo_contdiff : ContDiffOn 𝕜 n homeo.toFun homeo.source := by
    intro x hx
    have : homeo.source ⊆ U := subset_trans inter_subset_right inter_subset_left
    exact (hg.contDiffWithinAt (this hx)).mono this
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
      have source_nhd : homeo.source ∈ nhds (homeo.symm y) :=
        mem_nhds_iff.mpr ⟨homeo.source, subset_refl _, homeo.open_source, homeo.map_target hy⟩
      have : DifferentiableAt 𝕜 homeo (homeo.symm y) := (homeo_contdiff.differentiableOn hn
        (homeo.symm y) (homeo.map_target hy)).differentiableAt source_nhd
      exact (homeo.contDiffAt_symm hy (hg' ▸ this.hasFDerivAt)
        (homeo_contdiff.contDiffAt source_nhd)).contDiffWithinAt
  }

lemma toPartialDiffeomorph_mem_source : p ∈ (hg.toPartialDiffeomorph hU hpU hg' hn).source :=
  ⟨(hg.contDiffAt (hU.mem_nhds hpU)).mem_toOpenPartialHomeomorph_source hg' hn,
    hpU, f', Eq.symm (HasFDerivAt.fderiv hg')⟩

end ContDiffOn

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {n : WithTop ℕ∞} [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]

/-- The inverse function theorem for manifolds. If `f` is `ContMDiff` on a neighborhood of an
interior point `p` and has bijective differential at `p`, then `f` is a local diffeomorphism at `p`.
-/
theorem isLocalDiffeomorphAt_of_bijective_mfderiv {p : M₁} (hp : I₁.IsInteriorPoint p) {A : Set M₁}
    (hA : IsOpen A) (hpA : p ∈ A) {f : M₁ → M₂} (hf : ContMDiffOn I₁ I₂ n f A)
    (hf' : (mfderiv I₁ I₂ f p).ker = ⊥ ∧ (mfderiv I₁ I₂ f p).range = ⊤) (hn : n ≠ 0) :
    IsLocalDiffeomorphAt I₁ I₂ n f p := by
  -- show that `f p` is an interior point of `M₂`
  have mDiffAt_f_p : MDiffAt f p := (hf.contMDiffAt (hA.mem_nhds hpA)).mdifferentiableAt hn
  have hfp : I₂.IsInteriorPoint (f p) :=
    mDiffAt_f_p.isInteriorPoint_of_surjective_mfderiv (LinearMap.range_eq_top.mp hf'.2) hp
  -- let `g` be the coordinate representation of `f` and obtain coordinate charts
  set g : E₁ → E₂ := writtenInExtChartAt I₁ I₂ p f
  set φ₀ : PartialEquiv M₁ E₁ := extChartAt I₁ p
  set ψ₀ : PartialEquiv M₂ E₂ := extChartAt I₂ (f p)
  set φ₁ : PartialDiffeomorph I₁ 𝓘(𝕜, E₁) M₁ E₁ n := diffeoExtChartAt n hp
  set ψ₁ : PartialDiffeomorph I₂ 𝓘(𝕜, E₂) M₂ E₂ n := diffeoExtChartAt n hfp
  -- define `U ⊆ E₁`, an open set where we can easily show that `g` is ContDiff
  set U : Set E₁ := φ₁ '' (φ₁.source ∩ (A ∩ f ⁻¹' ψ₁.source))
  have U_open : IsOpen U := by
    refine φ₁.toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ inter_subset_left
    exact φ₁.open_source.inter (hf.continuousOn.isOpen_inter_preimage hA ψ₁.open_source)
  have hg : ContDiffOn 𝕜 n g U := by
    refine ((contMDiffOn_iff.mp hf).2 p (f p)).mono ?_
    rintro e ⟨m, ⟨hm₁, hm₂, hm₃⟩, rfl⟩
    refine ⟨diffeoExtChartAt_target_subset n hp (φ₁.map_source hm₁), ?_⟩
    simp only [mem_preimage] at hm₃ ⊢
    rw [eqOn_diffeoExtChartAt_extChartAt n hp hm₁,
      φ₀.left_inv (diffeoExtChartAt_source_subset n hp hm₁)]
    exact ⟨hm₂, diffeoExtChartAt_source_subset n hfp hm₃⟩
  have φ₀p_mem_U : φ₀ p ∈ U := mem_image_of_mem _ ⟨mem_diffeoExtChartAt_source n hp, hpA,
    mem_diffeoExtChartAt_source (n := n) hfp⟩
  have U_nhd : U ∈ nhds (φ₀ p) := mem_nhds_iff.mpr ⟨U, subset_refl _, U_open, φ₀p_mem_U⟩
  -- use `hf'` to show that the derivative of `g` at `φ₀ p` is a continuous linear equivalence
  have ⟨g', hg'⟩ : ∃ g' : E₁ ≃L[𝕜] E₂, HasFDerivAt g (g' : E₁ →L[𝕜] E₂) (φ₀ p) := by
    rw [mfderiv, if_pos mDiffAt_f_p] at hf'
    use ContinuousLinearEquiv.ofBijective (fderivWithin 𝕜 g (range I₁) (φ₀ p)) hf'.1 hf'.2
    exact mDiffAt_f_p.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt.hasFDerivAt
      (range_mem_nhds_isInteriorPoint hp)
  /- obtain partial diffeomorphism in coordinates and compose with the charts to obtain a partial
  diffeomorphism `M₁ → M₂` -/
  set coord_diffeo := hg.toPartialDiffeomorph U_open φ₀p_mem_U  hg' hn
  set diffeo := (φ₁.trans coord_diffeo).trans ψ₁.symm
  use diffeo
  constructor
  · refine ⟨⟨mem_diffeoExtChartAt_source n hp,
      (hg.toPartialDiffeomorph_mem_source U_open φ₀p_mem_U hg' hn)⟩, ?_⟩
    change (ψ₁ ∘ f ∘ φ₀.symm) (φ₀ p) ∈ ψ₁.target
    suffices ψ₁ (f p) ∈ ψ₁.target by simpa [φ₀.left_inv (mem_extChartAt_source p)]
    exact ψ₁.map_source (mem_diffeoExtChartAt_source n hfp)
  · intro m hm
    change f m = ψ₀.symm (ψ₀ (f (φ₀.symm (φ₀ m))))
    rw[φ₀.left_inv ((diffeoExtChartAt_source_subset n hp) hm.1.1), ψ₀.left_inv ?_]
    exact (diffeoExtChartAt_source_subset n hfp)
      (φ₁.injOn.mem_of_mem_image inter_subset_left hm.1.1 hm.1.2.2.1).2.2

end ManifoldInverseFunctionTheorem
