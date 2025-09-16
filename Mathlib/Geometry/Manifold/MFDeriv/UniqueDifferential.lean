/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Unique derivative sets in manifolds

In this file, we prove various properties of unique derivative sets in manifolds.
* `image_denseRange`: suppose `f` is differentiable on `s` and its derivative at every point of `s`
  has dense range. If `s` has the unique differential property, then so does `f '' s`.
* `uniqueMDiffOn_preimage`: the unique differential property is preserved by local diffeomorphisms
* `uniqueDiffOn_target_inter`: the unique differential property is preserved by
  pullbacks of extended charts
* `tangentBundle_proj_preimage`: if `s` has the unique differential property,
  its preimage under the tangent bundle projection also has
-/

noncomputable section

open scoped Manifold
open Set

/-! ### Unique derivative sets in manifolds -/

section UniqueMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H' M'']
  {s : Set M} {x : M}

section

/-- If `s` has the unique differential property at `x`, `f` is differentiable within `s` at `x` and
its derivative has dense range, then `f '' s` has the unique differential property at `f x`. -/
theorem UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffWithinAt I s x)
    {f : M → M'} {f' : E →L[𝕜] E'} (hf : HasMFDerivWithinAt I I' f s x f')
    (hd : DenseRange f') : UniqueMDiffWithinAt I' (f '' s) (f x) := by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
  have := hs.inter' <| hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

/-- If `s` has the unique differential property, `f` is differentiable on `s` and its derivative
at every point of `s` has dense range, then `f '' s` has the unique differential property.
This version uses the `HasMFDerivWithinAt` predicate. -/
theorem UniqueMDiffOn.image_denseRange' (hs : UniqueMDiffOn I s) {f : M → M'}
    {f' : M → E →L[𝕜] E'} (hf : ∀ x ∈ s, HasMFDerivWithinAt I I' f s x (f' x))
    (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueMDiffOn I' (f '' s) :=
  forall_mem_image.2 fun x hx ↦ (hs x hx).image_denseRange (hf x hx) (hd x hx)

/-- If `s` has the unique differential property, `f` is differentiable on `s` and its derivative
at every point of `s` has dense range, then `f '' s` has the unique differential property. -/
theorem UniqueMDiffOn.image_denseRange (hs : UniqueMDiffOn I s) {f : M → M'}
    (hf : MDifferentiableOn I I' f s) (hd : ∀ x ∈ s, DenseRange (mfderivWithin I I' f s x)) :
    UniqueMDiffOn I' (f '' s) :=
  hs.image_denseRange' (fun x hx ↦ (hf x hx).hasMFDerivWithinAt) hd

protected theorem UniqueMDiffWithinAt.preimage_partialHomeomorph (hs : UniqueMDiffWithinAt I s x)
    {e : PartialHomeomorph M M'} (he : e.MDifferentiable I I') (hx : x ∈ e.source) :
    UniqueMDiffWithinAt I' (e.target ∩ e.symm ⁻¹' s) (e x) := by
  rw [← e.image_source_inter_eq', inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
theorem UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiffOn I s) {e : PartialHomeomorph M M'}
    (he : e.MDifferentiable I I') : UniqueMDiffOn I' (e.target ∩ e.symm ⁻¹' s) := fun _x hx ↦
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_partialHomeomorph he (e.map_target hx.1)

variable [IsManifold I 1 M] in
/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem UniqueMDiffOn.uniqueMDiffOn_target_inter (hs : UniqueMDiffOn I s) (x : M) :
    UniqueMDiffOn 𝓘(𝕜, E) ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) := by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  rw [← PartialEquiv.image_source_inter_eq', inter_comm, extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy ↦ hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy ↦ ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange

variable [IsManifold I 1 M] in
/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiffOn I s) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
  (hs.uniqueMDiffOn_target_inter x).uniqueDiffOn

variable [IsManifold I 1 M] in
theorem UniqueMDiffOn.uniqueDiffWithinAt_range_inter (hs : UniqueMDiffOn I s) (x : M) (y : E)
    (hy : y ∈ (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :
    UniqueDiffWithinAt 𝕜 (range I ∩ (extChartAt I x).symm ⁻¹' s) y := by
  apply (hs.uniqueDiffOn_target_inter x y hy).mono
  apply inter_subset_inter_left _ (extChartAt_target_subset_range x)

variable [IsManifold I 1 M] in
/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiffOn I s) (x : M) (y : M'')
    {f : M → M''} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiffOn I (s ∩ f ⁻¹' (extChartAt I' y).source) := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

end

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Z : M → Type*}
  [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)] [FiberBundle F Z]

private lemma UniqueMDiffWithinAt.bundle_preimage_aux {p : TotalSpace F Z}
    (hs : UniqueMDiffWithinAt I s p.proj) (h's : s ⊆ (trivializationAt F Z p.proj).baseSet) :
    UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) p := by
  suffices ((extChartAt I p.proj).symm ⁻¹' s ∩ range I) ×ˢ univ ⊆
      (extChartAt (I.prod 𝓘(𝕜, F)) p).symm ⁻¹' (TotalSpace.proj ⁻¹' s) ∩ range (I.prod 𝓘(𝕜, F)) by
    let w := (extChartAt (I.prod 𝓘(𝕜, F)) p p).2
    have A : extChartAt (I.prod 𝓘(𝕜, F)) p p = (extChartAt I p.1 p.1, w) := by
      ext
      · simp [FiberBundle.chartedSpace_chartAt]
      · rfl
    simp only [UniqueMDiffWithinAt, A] at hs ⊢
    exact (hs.prod (uniqueDiffWithinAt_univ (x := w))).mono this
  rcases p with ⟨x, v⟩
  dsimp
  rintro ⟨z, w⟩ ⟨hz, -⟩
  simp only [mem_inter_iff, mem_preimage, Function.comp_apply,
    mem_range] at hz
  simp only [FiberBundle.chartedSpace_chartAt, PartialHomeomorph.coe_trans_symm, mem_inter_iff,
    mem_preimage, Function.comp_apply, mem_range]
  constructor
  · rw [PartialEquiv.prod_symm, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.refl_coe,
      PartialHomeomorph.prod_symm, PartialHomeomorph.refl_symm, PartialHomeomorph.prod_apply,
      PartialHomeomorph.refl_apply]
    convert hz.1
    apply Trivialization.proj_symm_apply'
    exact h's hz.1
  · rcases hz.2 with ⟨u, rfl⟩
    exact ⟨(u, w), rfl⟩

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. -/
theorem UniqueMDiffWithinAt.bundle_preimage {p : TotalSpace F Z}
    (hs : UniqueMDiffWithinAt I s p.proj) :
    UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) p := by
  suffices UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F))
    (π F Z ⁻¹' (s ∩ (trivializationAt F Z p.proj).baseSet)) p from this.mono (by simp)
  apply UniqueMDiffWithinAt.bundle_preimage_aux (hs.inter _) inter_subset_right
  exact IsOpen.mem_nhds (trivializationAt F Z p.proj).open_baseSet
    (FiberBundle.mem_baseSet_trivializationAt' p.proj)

variable (Z)

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. Version with a point `⟨b, x⟩`. -/
theorem UniqueMDiffWithinAt.bundle_preimage' {b : M} (hs : UniqueMDiffWithinAt I s b)
    (x : Z b) : UniqueMDiffWithinAt (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) ⟨b, x⟩ :=
  hs.bundle_preimage (p := ⟨b, x⟩)

/-- In a fiber bundle, the preimage under the projection of a set with unique differentials
in the base has unique differentials in the bundle. -/
theorem UniqueMDiffOn.bundle_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn (I.prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) := fun _p hp ↦
  (hs _ hp).bundle_preimage

-- TODO: move me to `Mathlib/Geometry/Manifold/VectorBundle/MDifferentiable.lean`
variable [∀ b, AddCommMonoid (Z b)] [∀ b, Module 𝕜 (Z b)] [VectorBundle 𝕜 F Z]

theorem Trivialization.mdifferentiable [ContMDiffVectorBundle 1 F Z I]
    (e : Trivialization F (π F Z)) [MemTrivializationAtlas e] :
    e.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) :=
  ⟨e.contMDiffOn.mdifferentiableOn le_rfl, e.contMDiffOn_symm.mdifferentiableOn le_rfl⟩

end UniqueMDiff
