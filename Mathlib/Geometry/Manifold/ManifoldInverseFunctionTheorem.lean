/-
Copyright (c) 2025 Matthew Spillman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Spillman
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.IsLocalHomeomorph

open Manifold Set TopologicalSpace

section DiffeoExtChartAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞)

/-- If p is an interior point of M, then (extChartAt I p) can be restricted to an open set
on which it becomes a PartialDiffeomorph (viewing E as a manifold modeled on itself trivially) -/
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
    suffices ContDiffOn 𝕜 n f s by simpa
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
    p ∈ (diffeoExtChartAt n hp).source := by
  suffices I ((chartAt H p) p) ∈ Classical.choose hp by
    simpa [diffeoExtChartAt, openPartialHomeomorph_of_isInteriorPoint]
  exact (Classical.choose_spec hp).2

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

open PartialDiffeomorph

-- need to redefine variables (this time with RCLike 𝕜) to prevent typeclass resolution conflicts
variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {n : WithTop ℕ∞} [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]

theorem localDiffeomorph_of_mfderiv_iso (hn : n ≠ 0) {f : M₁ → M₂} {p : M₁}
    (hp : I₁.IsInteriorPoint p) {A : Set M₁} (hA : IsOpen A) (hpA : p ∈ A)
    (hf : ContMDiffOn I₁ I₂ n f A)
    (hf' : (mfderiv I₁ I₂ f p).ker = ⊥ ∧ (mfderiv I₁ I₂ f p).range = ⊤) :
    IsLocalDiffeomorphAt I₁ I₂ n f p := by
  /-
  question : would it be better to have `f'` (linear equiv) and `HasMFDerivAt f p f'` as hypotheses?
  The `hf`' hypothesis and the process of using it to obtain `g'` seems a bit awkward
  -/

  -- obtain that `f p` is an interior point of `M₂`
  have A_nhd : A ∈ nhds p := hA.mem_nhds hpA
  have hfp : I₂.IsInteriorPoint (f p) := by
    have f_mdiffat_p := ((hf.contMDiffAt A_nhd).mdifferentiableAt hn)
    exact f_mdiffat_p.isInteriorPoint_of_surjective_mfderiv (LinearMap.range_eq_top.mp hf'.2) hp
  -- write the function in coordinates and obtain coordinate charts
  set g : E₁ → E₂ := writtenInExtChartAt I₁ I₂ p f
  set φ₀ := extChartAt I₁ p
  set φ₁ := diffeoExtChartAt n hp
  set ψ₀ := extChartAt I₂ (f p)
  set ψ₁ := diffeoExtChartAt n hfp
  -- define `U ⊆ E₁`, an open set where we can easily show that `g` is ContDiff
  set U : Set E₁ := φ₁ '' (φ₁.source ∩ (A ∩ f ⁻¹' ψ₁.source))
  have U_open : IsOpen U := by
    refine φ₁.toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ inter_subset_left
    exact φ₁.open_source.inter (hf.continuousOn.isOpen_inter_preimage hA ψ₁.open_source)
  have U_nhd : U ∈ nhds (φ₀ p) := mem_nhds_iff.mpr ⟨U, subset_refl _, U_open, mem_image_of_mem _
    ⟨mem_diffeoExtChartAt_source n hp, hpA, mem_diffeoExtChartAt_source (n := n) hfp⟩⟩
  have hg : ContDiffOn 𝕜 n g U := by
    refine ((contMDiffOn_iff.mp hf).2 p (f p)).mono ?_
    rintro e ⟨m, ⟨hm₁, hm₂, hm₃⟩, rfl⟩
    refine ⟨diffeoExtChartAt_target_subset n hp (φ₁.map_source hm₁), ?_⟩
    simp only [mem_preimage] at hm₃ ⊢
    rw [eqOn_diffeoExtChartAt_extChartAt n hp hm₁,
      φ₀.left_inv (diffeoExtChartAt_source_subset n hp hm₁)]
    exact ⟨hm₂, diffeoExtChartAt_source_subset n hfp hm₃⟩
  -- use `hf'` to show that the derivative of `g` at `φ₀ p` is a linear equivalence
  have ⟨g', hg'⟩ : ∃ g' : E₁ ≃L[𝕜] E₂, HasFDerivAt g (g' : E₁ →L[𝕜] E₂) (φ₀ p) := by
    have g_diff: DifferentiableWithinAt 𝕜 g (range I₁) (φ₀ p) :=
      ((hg.differentiableOn hn).differentiableAt U_nhd).differentiableWithinAt
    rw [mfderiv, if_pos ((hf.contMDiffAt A_nhd).mdifferentiableAt hn), fderivWithin] at hf'
    by_cases g'_zero: HasFDerivWithinAt g (0 : E₁ →L[𝕜] E₂) (range I₁) (φ₀ p)
    · rw [if_pos g'_zero] at hf'
      exact ⟨ContinuousLinearEquiv.ofBijective 0 hf'.1 hf'.2,
        g'_zero.hasFDerivAt (range_mem_nhds_isInteriorPoint hp)⟩
    · rw [if_neg g'_zero, dif_pos g_diff] at hf'
      exact ⟨ContinuousLinearEquiv.ofBijective (Classical.choose g_diff) hf'.1 hf'.2,
        (Classical.choose_spec g_diff).hasFDerivAt (range_mem_nhds_isInteriorPoint hp)⟩
  -- define `V`, the open set where `g'` is a linear equivalence
  set V := fderiv 𝕜 g ⁻¹' range ContinuousLinearEquiv.toContinuousLinearMap
  have hUV: IsOpen (U ∩ V) :=
    (hg.continuousOn_fderiv_of_isOpen U_open (ENat.one_le_iff_ne_zero_withTop.mpr hn)
    ).isOpen_inter_preimage U_open (ContinuousLinearEquiv.isOpen)
  /- obtain an `OpenPartialHomeomorph E → F` using the standard inverse function theorem. We must
  restrict to `U ∩ V` so that we can later show ContDiff of the forward and inverse function
  todo : refactor this part to a separate function since it could be independently useful? -/
  set homeo := ((hg.contDiffAt U_nhd).toOpenPartialHomeomorph g hg' hn).restrOpen _ hUV
  have homeo_source_sub_UV : homeo.source ⊆ U ∩ V :=
    ((hg.contDiffAt U_nhd).toOpenPartialHomeomorph g hg' hn).restrOpen_source _ hUV ▸
    inter_subset_right
  have homeo_contdiff : ContDiffOn 𝕜 n homeo.toFun homeo.source := by
    intro x hx
    have : homeo.source ⊆ U := subset_trans homeo_source_sub_UV inter_subset_left
    exact (hg.contDiffWithinAt (this hx)).mono (subset_trans homeo_source_sub_UV inter_subset_left)
  -- upgrade to a `PartialDiffeomorph` using the properties of `U` and `V`
  set coord_diffeo : PartialDiffeomorph 𝓘(𝕜, E₁) 𝓘(𝕜, E₂) E₁ E₂ n := {
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
      rcases (subset_trans homeo_source_sub_UV inter_subset_right) (homeo.map_target hy) with
        ⟨g', hg'⟩
      have source_nhd : homeo.source ∈ nhds (homeo.symm y) :=
        mem_nhds_iff.mpr ⟨homeo.source, subset_refl _, homeo.open_source, homeo.map_target hy⟩
      have : DifferentiableAt 𝕜 homeo (homeo.symm y) := (homeo_contdiff.differentiableOn hn
        (homeo.symm y) (homeo.map_target hy)).differentiableAt source_nhd
      exact (homeo.contDiffAt_symm hy (hg' ▸ this.hasFDerivAt)
        (homeo_contdiff.contDiffAt source_nhd)).contDiffWithinAt
  }
  -- compose with the charts to obtain our partial diffeomorphism `M → N`
  set diffeo := (φ₁.trans coord_diffeo).trans ψ₁.symm
  use diffeo
  -- rote verification of remaining conditions, mostly just unwrapping definitions (todo: clean up)
  constructor
  · show p ∈ diffeo.source
    simp [diffeo, PartialDiffeomorph.trans, toOpenPartialHomeomorph, coord_diffeo, homeo, U, V,
      and_assoc]
    refine ⟨mem_diffeoExtChartAt_source n hp,
      ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _,
      ⟨p, mem_diffeoExtChartAt_source n hp, hpA, mem_diffeoExtChartAt_source n hfp, rfl⟩,
      ⟨g', hg'.fderiv.symm⟩,
      ?_⟩
    suffices ψ₁ (f p) ∈ ψ₁.symm.source by
      simpa [g, φ₁, diffeoExtChartAt, openPartialHomeomorph_of_isInteriorPoint]
    exact ψ₁.map_source (mem_diffeoExtChartAt_source n hfp)
  · show EqOn f diffeo diffeo.source
    intro m hm
    suffices f m = (chartAt H₂ (f p)).symm
      ((chartAt H₂ (f p)) (f ((chartAt H₁ p).symm ((chartAt H₁ p) m)))) by
      simpa [diffeo, PartialDiffeomorph.trans, φ₁, ψ₁, toOpenPartialHomeomorph, diffeoExtChartAt,
        coord_diffeo, homeo, PartialDiffeomorph.symm, openPartialHomeomorph_of_isInteriorPoint, g]
    rw [(chartAt H₁ p).left_inv
      (extChartAt_source I₁ p ▸ (diffeoExtChartAt_source_subset (n := n) hp) hm.1.1),
      (chartAt H₂ (f p)).left_inv ?_]
    rcases hm.1.2.2.1 with ⟨m', hm'₁, hm'₂⟩
    have : m' = m := by
      calc m' = φ₁.symm (φ₁ m') := (φ₁.left_inv hm'₁.1).symm
      _ = φ₁.symm (φ₁ m) := by congr 1
      _ = m := (φ₁.left_inv hm.1.1)
    subst this
    exact extChartAt_source I₂ (f p) ▸ diffeoExtChartAt_source_subset (n := n) hfp hm'₁.2.2

end ManifoldInverseFunctionTheorem
