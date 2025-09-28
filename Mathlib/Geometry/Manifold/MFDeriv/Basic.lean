/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Basic properties of the manifold Fréchet derivative

In this file, we show various properties of the manifold Fréchet derivative,
mimicking the API for Fréchet derivatives.
- basic properties of unique differentiability sets
- various general lemmas about the manifold Fréchet derivative
- deducing differentiability from smoothness,
- deriving continuity from differentiability on manifolds,
- congruence lemmas for derivatives on manifolds
- composition lemmas and the chain rule

-/

noncomputable section

assert_not_exists tangentBundleCore

open scoped Topology Manifold
open Set Bundle ChartedSpace

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

theorem uniqueMDiffWithinAt_univ : UniqueMDiffWithinAt I univ x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

variable {I}

theorem uniqueMDiffWithinAt_iff_inter_range {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) := Iff.rfl

theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : 𝓝[s] x ≤ 𝓝[t] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds <| by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

theorem UniqueMDiffWithinAt.mono_of_mem_nhdsWithin {s t : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)

theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
    UniqueMDiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)

theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)

theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.inter' (nhdsWithin_le_nhds ht)

theorem IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueMDiffWithinAt I s x :=
  (uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin <| nhdsWithin_le_nhds <| hs.mem_nhds xs

theorem UniqueMDiffOn.inter (hs : UniqueMDiffOn I s) (ht : IsOpen t) : UniqueMDiffOn I (s ∩ t) :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)

theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiffOn I s :=
  fun _x hx => hs.uniqueMDiffWithinAt hx

theorem uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M) :=
  isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s t} (hs : UniqueMDiffWithinAt I s x)
    (ht : UniqueMDiffWithinAt I' t y) : UniqueMDiffWithinAt (I.prod I') (s ×ˢ t) (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod, ← prod_inter_prod]
  rfl

theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiffOn I s)
    (ht : UniqueMDiffOn I' t) : UniqueMDiffOn (I.prod I') (s ×ˢ t) := fun x h ↦
  (hs x.1 h.1).prod (ht x.2 h.2)

theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
    MDifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩

theorem mdifferentiableWithinAt_univ :
    MDifferentiableWithinAt I I' f univ x ↔ MDifferentiableAt I I' f x := by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]

theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]

theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]

theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDifferentiableAt I I' f x) :
    MDifferentiableWithinAt I I' f s x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDifferentiableWithinAt I I' f s x)
    (hs : s ∈ 𝓝 x) : MDifferentiableAt I I' f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
    MDifferentiableOn I I' f s := fun x hx => (h x (st hx)).mono st

theorem mdifferentiableOn_univ : MDifferentiableOn I I' f univ ↔ MDifferentiable I I' f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl

theorem MDifferentiableOn.mdifferentiableAt (h : MDifferentiableOn I I' f s) (hx : s ∈ 𝓝 x) :
    MDifferentiableAt I I' f x :=
  (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

theorem MDifferentiable.mdifferentiableOn (h : MDifferentiable I I' f) :
    MDifferentiableOn I I' f s :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)

theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MDifferentiableOn I I' f (s ∩ u)) :
    MDifferentiableOn I I' f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)

theorem MDifferentiable.mdifferentiableAt (hf : MDifferentiable I I' f) :
    MDifferentiableAt I I' f x :=
  hf x

/-!
### Relating differentiability in a manifold and differentiability in the model space
through extended charts
-/


theorem mdifferentiableWithinAt_iff_target_inter {f : M → M'} {s : Set M} {x : M} :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
theorem mdifferentiableWithinAt_iff :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [MDifferentiableWithinAt, ChartedSpace.liftPropWithinAt_iff']; rfl

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `mdifferentiableWithinAt_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
theorem mdifferentiableWithinAt_iff_target_inter' :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [MDifferentiableWithinAt, liftPropWithinAt_iff']
  exact and_congr_right fun hc => differentiableWithinAt_congr_nhds <|
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
theorem mdifferentiableWithinAt_iff_target :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
      MDifferentiableWithinAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [MDifferentiableWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
      and_iff_left_of_imp <| (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, DifferentiableWithinAtProp, extChartAt, PartialHomeomorph.extend,
    PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.coe_coe, modelWithCornersSelf_coe,
    chartAt_self_eq, PartialHomeomorph.refl_apply]
  rfl

theorem mdifferentiableAt_iff_target {x : M} :
    MDifferentiableAt I I' f x ↔
      ContinuousAt f x ∧ MDifferentiableAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ, ← mdifferentiableWithinAt_univ,
    mdifferentiableWithinAt_iff_target, continuousWithinAt_univ]

section IsManifold

variable {e : PartialHomeomorph M H} {e' : PartialHomeomorph M' H'}

open IsManifold

theorem mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
    [IsManifold I 1 M] (he : e ∈ maximalAtlas I 1 M) (hx : x ∈ e.source) :
    MDifferentiableWithinAt I I' f s x ↔
      MDifferentiableWithinAt 𝓘(𝕜, E) I' (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s ∩ range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, differentiableWithinAtProp_self_source,
    DifferentiableWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

theorem mdifferentiableWithinAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      MDifferentiableWithinAt 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

theorem mdifferentiableAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    MDifferentiableAt I I' f x' ↔
      MDifferentiableWithinAt 𝓘(𝕜, E) I' (f ∘ (extChartAt I x).symm) (range I)
        (extChartAt I x x') := by
  simp_rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_source_of_mem_source hx',
    preimage_univ, univ_inter]

theorem mdifferentiableWithinAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧ MDifferentiableWithinAt I 𝓘(𝕜, E') (extChartAt I' y ∘ f) s x := by
  simp_rw [MDifferentiableWithinAt]
  rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy,
    and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl

theorem mdifferentiableAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    MDifferentiableAt I I' f x ↔
      ContinuousAt f x ∧ MDifferentiableAt I 𝓘(𝕜, E') (extChartAt I' y ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_target_of_mem_source hy,
    continuousWithinAt_univ, ← mdifferentiableWithinAt_univ]

variable [IsManifold I 1 M] [IsManifold I' 1 M']

theorem mdifferentiableWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hy

/-- An alternative formulation of `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`
if the set if `s` lies in `e.source`. -/
theorem mdifferentiableWithinAt_iff_image {x : M} (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (hx : x ∈ e.source)
    (hy : f x ∈ e'.source) :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine fun _ => differentiableWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
theorem mdifferentiableWithinAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. Version requiring differentiability
in the target instead of `range I`. -/
theorem mdifferentiableWithinAt_iff_of_mem_source' {x' : M} {y : M'}
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => differentiableWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image' hx,
    ← map_extChartAt_nhdsWithin' hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)

theorem mdifferentiableAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    MDifferentiableAt I I' f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]

theorem mdifferentiableOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    MDifferentiableOn I I' f s ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, DifferentiableOn, Set.forall_mem_image, ← forall_and, MDifferentiableOn]
  exact forall₂_congr fun x hx => mdifferentiableWithinAt_iff_image he he' hs (hs hx) (h2s hx)

/-- Differentiability on a set is equivalent to differentiability in the extended charts. -/
theorem mdifferentiableOn_iff_of_mem_maximalAtlas' (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    MDifferentiableOn I I' f s ↔
      DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  (mdifferentiableOn_iff_of_mem_maximalAtlas he he' hs h2s).trans <| and_iff_right_of_imp fun h ↦
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
theorem mdifferentiableOn_iff_of_subset_source {x : M} {y : M'} (hs : s ⊆ (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    MDifferentiableOn I I' f s ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  mdifferentiableOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
theorem mdifferentiableOn_iff_of_subset_source' {x : M} {y : M'} (hs : s ⊆ (extChartAt I x).source)
    (h2s : MapsTo f s (extChartAt I' y).source) :
    MDifferentiableOn I I' f s ↔
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact mdifferentiableOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
theorem mdifferentiableOn_iff :
    MDifferentiableOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w ∈ s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w ∈ (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w ∈ (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert ((mdifferentiableWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine differentiableWithinAt_localInvariantProp.liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [DifferentiableWithinAtProp]
    convert hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
theorem mdifferentiableOn_iff_target :
    MDifferentiableOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ y : M', MDifferentiableOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f)
          (s ∩ f ⁻¹' (extChartAt I' y).source) := by
  simp only [mdifferentiableOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    PartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
theorem mdifferentiable_iff :
    MDifferentiable I I' f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) := by
  simp [← mdifferentiableOn_univ, mdifferentiableOn_iff, continuousOn_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
theorem mdifferentiable_iff_target :
    MDifferentiable I I' f ↔
      Continuous f ∧ ∀ y : M',
        MDifferentiableOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) := by
  rw [← mdifferentiableOn_univ, mdifferentiableOn_iff_target]
  simp [continuousOn_univ]

end IsManifold

/-! ### Deducing differentiability from smoothness -/

variable {n : WithTop ℕ∞}

theorem ContMDiffWithinAt.mdifferentiableWithinAt (hf : ContMDiffWithinAt I I' n f s x)
    (hn : 1 ≤ n) : MDifferentiableWithinAt I I' f s x := by
  suffices h : MDifferentiableWithinAt I I' f (s ∩ f ⁻¹' (extChartAt I' (f x)).source) x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt (mod_cast hn)).mono
    (by mfld_set_tac)⟩

theorem ContMDiffAt.mdifferentiableAt (hf : ContMDiffAt I I' n f x) (hn : 1 ≤ n) :
    MDifferentiableAt I I' f x :=
  mdifferentiableWithinAt_univ.1 <| ContMDiffWithinAt.mdifferentiableWithinAt hf hn

theorem ContMDiff.mdifferentiableAt (hf : ContMDiff I I' n f) (hn : 1 ≤ n) :
    MDifferentiableAt I I' f x :=
  hf.contMDiffAt.mdifferentiableAt hn

theorem ContMDiff.mdifferentiableWithinAt (hf : ContMDiff I I' n f) (hn : 1 ≤ n) :
    MDifferentiableWithinAt I I' f s x :=
  (hf.contMDiffAt.mdifferentiableAt hn).mdifferentiableWithinAt

theorem ContMDiffOn.mdifferentiableOn (hf : ContMDiffOn I I' n f s) (hn : 1 ≤ n) :
    MDifferentiableOn I I' f s := fun x hx => (hf x hx).mdifferentiableWithinAt hn

theorem ContMDiff.mdifferentiable (hf : ContMDiff I I' n f) (hn : 1 ≤ n) : MDifferentiable I I' f :=
  fun x => (hf x).mdifferentiableAt hn

theorem MDifferentiableOn.continuousOn (h : MDifferentiableOn I I' f s) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt

theorem MDifferentiable.continuous (h : MDifferentiable I I' f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

/-! ### Deriving continuity from differentiability on manifolds -/

theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x) :
    MDifferentiableWithinAt I (I'.prod I'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

@[deprecated (since := "2025-03-08")]
alias MDifferentiableWithinAt.prod_mk := MDifferentiableWithinAt.prodMk

/-- If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`. -/
theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace I x →L[𝕜] TangentSpace I' (f x)} (hf : HasMFDerivWithinAt I I' f s x df)
    {dg : TangentSpace I x →L[𝕜] TangentSpace I'' (g x)} (hg : HasMFDerivWithinAt I I'' g s x dg) :
    HasMFDerivWithinAt I (I'.prod I'') (fun y ↦ (f y, g y)) s x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I'' g x) :
    MDifferentiableAt I (I'.prod I'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

@[deprecated (since := "2025-03-08")]
alias MDifferentiableAt.prod_mk := MDifferentiableAt.prodMk

/-- If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`. -/
theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace I x →L[𝕜] TangentSpace I' (f x)} (hf : HasMFDerivAt I I' f x df)
    {dg : TangentSpace I x →L[𝕜] TangentSpace I'' (g x)} (hg : HasMFDerivAt I I'' g x dg) :
    HasMFDerivAt I (I'.prod I'') (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableWithinAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E'') g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

@[deprecated (since := "2025-03-08")]
alias MDifferentiableWithinAt.prod_mk_space := MDifferentiableWithinAt.prodMk_space

theorem MDifferentiableAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) (hg : MDifferentiableAt I 𝓘(𝕜, E'') g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

@[deprecated (since := "2025-03-08")]
alias MDifferentiableAt.prod_mk_space := MDifferentiableAt.prodMk_space

theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn I I'' g s) :
    MDifferentiableOn I (I'.prod I'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

@[deprecated (since := "2025-03-08")]
alias MDifferentiableOn.prod_mk := MDifferentiableOn.prodMk

theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiable I I' f)
    (hg : MDifferentiable I I'' g) : MDifferentiable I (I'.prod I'') fun x => (f x, g x) := fun x =>
  (hf x).prodMk (hg x)

@[deprecated (since := "2025-03-08")]
alias MDifferentiable.prod_mk := MDifferentiable.prodMk

theorem MDifferentiableOn.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) (hg : MDifferentiableOn I 𝓘(𝕜, E'') g s) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk_space (hg x hx)

@[deprecated (since := "2025-03-08")]
alias MDifferentiableOn.prod_mk_space := MDifferentiableOn.prodMk_space

theorem MDifferentiable.prodMk_space {f : M → E'} {g : M → E''} (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E'') g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
  fun x => (hf x).prodMk_space (hg x)

@[deprecated (since := "2025-03-08")]
alias MDifferentiable.prod_mk_space := MDifferentiable.prodMk_space

theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    {y | writtenInExtChartAt I I'' x (g ∘ f) y =
          (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) y} ∈
      𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x := by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)))
  mfld_set_tac

variable {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
protected nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffWithinAt I s x)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' := by
  -- `by apply` because the instances can be found in the term but not in the goal.
  apply U.eq h.2 h₁.2

protected theorem UniqueMDiffOn.eq (U : UniqueMDiffOn I s) (hx : x ∈ s)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁

/-!
### General lemmas on derivatives of functions between manifolds

We mimic the API for functions between vector spaces
-/

@[simp, mfld_simps]
theorem mfderivWithin_univ : mfderivWithin I I' f univ = mfderiv I I' f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt
    (h : ¬MDifferentiableWithinAt I I' f s x) : mfderivWithin I I' f s x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDifferentiableAt I I' f x) :
    mfderiv I I' f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]

theorem mdifferentiable_of_subsingleton [Subsingleton E] : MDifferentiable I I' f := by
  intro x
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := discreteTopology H M
  simp only [mdifferentiableAt_iff, continuous_of_discreteTopology.continuousAt, true_and]
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

theorem mdifferentiableWithinAt_of_isInvertible_mfderivWithin
    (hf : (mfderivWithin I I' f s x).IsInvertible) : MDifferentiableWithinAt I I' f s x := by
  contrapose hf
  rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hf]
  contrapose! hf
  rcases ContinuousLinearMap.isInvertible_zero_iff.1 hf with ⟨hE, hF⟩
  have : Subsingleton E := hE
  exact mdifferentiable_of_subsingleton.mdifferentiableAt.mdifferentiableWithinAt

theorem mdifferentiableAt_of_isInvertible_mfderiv
    (hf : (mfderiv I I' f x).IsInvertible) : MDifferentiableAt I I' f x := by
  simp only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] at hf ⊢
  exact mdifferentiableWithinAt_of_isInvertible_mfderivWithin hf

theorem HasMFDerivWithinAt.mono (h : HasMFDerivWithinAt I I' f t x f') (hst : s ⊆ t) :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt I I' f x f') :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩

theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    MDifferentiableWithinAt I I' f s x :=
  ⟨h.1, ⟨f', h.2⟩⟩

theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt I I' f x f') :
    MDifferentiableAt I I' f x := by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]
theorem hasMFDerivWithinAt_univ :
    HasMFDerivWithinAt I I' f univ x f' ↔ HasMFDerivAt I I' f x f' := by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]

theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt I I' f x f₀') (h₁ : HasMFDerivAt I I' f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

theorem hasMFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq,
    hasFDerivWithinAt_inter', continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin h

theorem hasMFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq, hasFDerivWithinAt_inter,
    continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds h

theorem HasMFDerivWithinAt.union (hs : HasMFDerivWithinAt I I' f s x f')
    (ht : HasMFDerivWithinAt I I' f t x f') : HasMFDerivWithinAt I I' f (s ∪ t) x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]

theorem HasMFDerivWithinAt.mono_of_mem_nhdsWithin
    (h : HasMFDerivWithinAt I I' f s x f') (ht : s ∈ 𝓝[t] x) :
    HasMFDerivWithinAt I I' f t x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)

theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivWithinAt I I' f s x f') (hs : s ∈ 𝓝 x) :
    HasMFDerivAt I I' f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h

theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    HasMFDerivWithinAt I I' f s x (mfderivWithin I I' f s x) := by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

theorem mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt :
    MDifferentiableWithinAt I I' f s x ↔ ∃ f', HasMFDerivWithinAt I I' f s x f' := by
  refine ⟨fun h ↦ ⟨mfderivWithin I I' f s x, h.hasMFDerivWithinAt⟩, ?_⟩
  rintro ⟨f', hf'⟩
  exact hf'.mdifferentiableWithinAt

theorem MDifferentiableWithinAt.mono_of_mem_nhdsWithin
    (h : MDifferentiableWithinAt I I' f s x) {t : Set M}
    (hst : s ∈ 𝓝[t] x) : MDifferentiableWithinAt I I' f t x :=
  (h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin hst).mdifferentiableWithinAt

theorem MDifferentiableWithinAt.congr_nhds (h : MDifferentiableWithinAt I I' f s x) {t : Set M}
    (hst : 𝓝[s] x = 𝓝[t] x) : MDifferentiableWithinAt I I' f t x :=
  h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin

theorem mdifferentiableWithinAt_congr_nhds {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

protected theorem MDifferentiableWithinAt.mfderivWithin (h : MDifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) := by
  simp only [mfderivWithin, h, if_pos]

theorem MDifferentiableAt.hasMFDerivAt (h : MDifferentiableAt I I' f x) :
    HasMFDerivAt I I' f x (mfderiv I I' f x) := by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt

protected theorem MDifferentiableAt.mfderiv (h : MDifferentiableAt I I' f x) :
    mfderiv I I' f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) (range I) ((extChartAt I x) x) := by
  simp only [mfderiv, h, if_pos]

protected theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt I I' f x f') : mfderiv I I' f x = f' :=
  (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm

protected theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivWithinAt I I' f s x f')
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]

theorem HasMFDerivWithinAt.mfderivWithin_eq_zero (h : HasMFDerivWithinAt I I' f s x 0) :
    mfderivWithin I I' f s x = 0 := by
  simp only [mfld_simps, mfderivWithin, h.mdifferentiableWithinAt, ↓reduceIte]
  simp only [HasMFDerivWithinAt, mfld_simps] at h
  rw [fderivWithin, if_pos]
  exact h.2

theorem MDifferentiable.mfderivWithin (h : MDifferentiableAt I I' f x)
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = mfderiv I I' f x := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt

theorem mfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffWithinAt I s x)
    (h : MDifferentiableWithinAt I I' f t x) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs

theorem mfderivWithin_inter (ht : t ∈ 𝓝 x) :
    mfderivWithin I I' f (s ∩ t) x = mfderivWithin I I' f s x := by
  rw [mfderivWithin, mfderivWithin, extChartAt_preimage_inter_eq, mdifferentiableWithinAt_inter ht,
    fderivWithin_inter (extChartAt_preimage_mem_nhds ht)]

theorem mfderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : mfderivWithin I I' f s x = mfderiv I I' f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]

lemma mfderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mfderivWithin I I' f s x = mfderiv I I' f x :=
  mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

theorem hasMFDerivWithinAt_insert {y : M} :
    HasMFDerivWithinAt I I' f (insert y s) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  have : T1Space M := I.t1Space M
  refine ⟨fun h => h.mono <| subset_insert y s, fun hf ↦ ?_⟩
  rcases eq_or_ne x y with rfl | h
  · rw [HasMFDerivWithinAt] at hf ⊢
    refine ⟨hf.1.insert, ?_⟩
    have : (extChartAt I x).target ∈
        𝓝[(extChartAt I x).symm ⁻¹' insert x s ∩ range I] (extChartAt I x) x :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)
    rw [← hasFDerivWithinAt_inter' this]
    apply hf.2.insert.mono
    rintro z ⟨⟨hz, h2z⟩, h'z⟩
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_range] at hz h2z ⊢
    rcases hz with xz | h'z
    · left
      have : x ∈ (extChartAt I x).source := mem_extChartAt_source x
      exact (((extChartAt I x).eq_symm_apply this h'z).1 xz.symm).symm
    · exact Or.inr ⟨h'z, h2z⟩
  · apply hf.mono_of_mem_nhdsWithin ?_
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨HasMFDerivWithinAt.of_insert, HasMFDerivWithinAt.insert'⟩ := hasMFDerivWithinAt_insert

protected theorem HasMFDerivWithinAt.insert (h : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt I I' f (insert x s) x f' :=
  h.insert'

theorem hasMFDerivWithinAt_diff_singleton (y : M) :
    HasMFDerivWithinAt I I' f (s \ {y}) x f' ↔ HasMFDerivWithinAt I I' f s x f' := by
  rw [← hasMFDerivWithinAt_insert, insert_diff_singleton, hasMFDerivWithinAt_insert]

theorem mfderivWithin_eq_mfderiv (hs : UniqueMDiffWithinAt I s x) (h : MDifferentiableAt I I' f x) :
    mfderivWithin I I' f s x = mfderiv I I' f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

theorem mdifferentiableWithinAt_insert_self :
    MDifferentiableWithinAt I I' f (insert x s) x ↔ MDifferentiableWithinAt I I' f s x :=
  ⟨fun h ↦ h.mono (subset_insert x s), fun h ↦ h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt⟩

theorem mdifferentiableWithinAt_insert {y : M} :
    MDifferentiableWithinAt I I' f (insert y s) x ↔ MDifferentiableWithinAt I I' f s x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mdifferentiableWithinAt_insert_self
  have : T1Space M := I.t1Space M
  apply mdifferentiableWithinAt_congr_nhds
  exact nhdsWithin_insert_of_ne h

alias ⟨MDifferentiableWithinAt.of_insert, MDifferentiableWithinAt.insert'⟩ :=
mdifferentiableWithinAt_insert

protected theorem MDifferentiableWithinAt.insert (h : MDifferentiableWithinAt I I' f s x) :
    MDifferentiableWithinAt I I' f (insert x s) x :=
  h.insert'

/-! ### Being differentiable on a union of open sets can be tested on each set -/

section mdifferentiableOn_union

/-- If a function is differentiable on two open sets, it is also differentiable on their union. -/
lemma MDifferentiableOn.union_of_isOpen
    (hf : MDifferentiableOn I I' f s) (hf' : MDifferentiableOn I I' f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    MDifferentiableOn I I' f (s ∪ t) := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).mdifferentiableAt (hs.mem_nhds hx) |>.mdifferentiableWithinAt
  · exact (hf' x hx).mdifferentiableAt (ht.mem_nhds hx) |>.mdifferentiableWithinAt

/-- A function is differentiable on two open sets iff it is differentiable on their union. -/
lemma mdifferentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    MDifferentiableOn I I' f (s ∪ t) ↔ MDifferentiableOn I I' f s ∧ MDifferentiableOn I I' f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ ↦ MDifferentiableOn.union_of_isOpen hfs hft hs ht⟩

lemma mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hf : MDifferentiableOn I I' f s)
    (hf' : MDifferentiableOn I I' f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    MDifferentiable I I' f := by
  rw [← mdifferentiableOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is differentiable on open sets `s i`, it is differentiable on their union. -/
lemma MDifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, MDifferentiableOn I I' f (s i)) (hs : ∀ i, IsOpen (s i)) :
    MDifferentiableOn I I' f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).mdifferentiableAt ((hs i).mem_nhds hxsi) |>.mdifferentiableWithinAt

/-- A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`. -/
lemma mdifferentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set M}
    (hs : ∀ i, IsOpen (s i)) :
    MDifferentiableOn I I' f (⋃ i, s i) ↔ ∀ i : ι, MDifferentiableOn I I' f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ MDifferentiableOn.iUnion_of_isOpen h hs⟩

lemma mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, MDifferentiableOn I I' f (s i))
    (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    MDifferentiable I I' f := by
  rw [← mdifferentiableOn_univ, ← hs']
  exact MDifferentiableOn.iUnion_of_isOpen hf hs

end mdifferentiableOn_union

/-! ### Deriving continuity from differentiability on manifolds -/

theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    ContinuousWithinAt f s x :=
  h.1

theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt I I' f x f') : ContinuousAt f x :=
  h.1

theorem tangentMapWithin_subset {p : TangentBundle I M} (st : s ⊆ t)
    (hs : UniqueMDiffWithinAt I s p.1) (h : MDifferentiableWithinAt I I' f t p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f t p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]

theorem tangentMapWithin_univ : tangentMapWithin I I' f univ = tangentMap I I' f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]

theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.1)
    (h : MDifferentiableAt I I' f p.1) : tangentMapWithin I I' f s p = tangentMap I I' f p := by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]
theorem tangentMapWithin_proj {p : TangentBundle I M} :
    (tangentMapWithin I I' f s p).proj = f p.proj :=
  rfl

@[simp, mfld_simps]
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap I I' f p).proj = f p.proj :=
  rfl

/-- If two sets coincide locally around `x`, except maybe at a point `y`, then their
preimage under `extChartAt x` coincide locally, except maybe at `extChartAt I x x`. -/
theorem preimage_extChartAt_eventuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E) =ᶠ[𝓝[{extChartAt I x x}ᶜ] (extChartAt I x x)]
    ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) := by
  have : T1Space M := I.t1Space M
  obtain ⟨u, u_mem, hu⟩ : ∃ u ∈ 𝓝 x, u ∩ {x}ᶜ ⊆ {y | (y ∈ s) = (y ∈ t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I:= I) x] at u_mem
  have B : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_setOf_eq]
  change z ∈ (extChartAt I x).symm ⁻¹' s ∩ range I ↔ z ∈ (extChartAt I x).symm ⁻¹' t ∩ range I
  by_cases hIz : z ∈ range I
  · simp [-extChartAt, hIz] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff, ne_comm, ne_eq] at h'z ⊢
    rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

/-! ### Congruence lemmas for derivatives on manifolds -/

/-- If two sets coincide locally, except maybe at a point, then it is equivalent to have a manifold
derivative within one or the other. -/
theorem hasMFDerivWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasMFDerivWithinAt I I' f s x f' ↔ HasMFDerivWithinAt I I' f t x f' := by
  have : T1Space M := I.t1Space M
  simp only [HasMFDerivWithinAt]
  refine and_congr ?_ ?_
  · exact continuousWithinAt_congr_set' _ h
  · apply hasFDerivWithinAt_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h

theorem hasMFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasMFDerivWithinAt I I' f s x f' ↔ HasMFDerivWithinAt I I' f t x f' :=
  hasMFDerivWithinAt_congr_set' x <| h.filter_mono inf_le_left

/-- If two sets coincide around a point (except possibly at a single point `y`), then it is
equivalent to be differentiable within one or the other set. -/
theorem mdifferentiableWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f t x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set' _ h

theorem mdifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f t x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set h

/-- If two sets coincide locally, except maybe at a point, then derivatives within these sets
are the same. -/
theorem mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x := by
  by_cases hx : MDifferentiableWithinAt I I' f s x
  · simp only [mfderivWithin, hx, (mdifferentiableWithinAt_congr_set' y h).1 hx, ↓reduceIte]
    apply fderivWithin_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
  · simp [mfderivWithin, hx, ← mdifferentiableWithinAt_congr_set' y h]

/-- If two sets coincide locally, then derivatives within these sets
are the same. -/
theorem mfderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  mfderivWithin_congr_set' x <| h.filter_mono inf_le_left

/-- If two sets coincide locally, except maybe at a point, then derivatives within these sets
coincide locally. -/
theorem mfderivWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ∀ᶠ y in 𝓝 x, mfderivWithin I I' f s y = mfderivWithin I I' f t y :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mfderivWithin_congr_set' y

/-- If two sets coincide locally, then derivatives within these sets coincide locally. -/
theorem mfderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    ∀ᶠ y in 𝓝 x, mfderivWithin I I' f s y = mfderivWithin I I' f t y :=
  mfderivWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt I I' f x f') (h' : f' = f₁') :
    HasMFDerivAt I I' f x f₁' :=
  h' ▸ h

theorem HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivWithinAt I I' f s x f') (h' : f' = f₁') :
    HasMFDerivWithinAt I I' f s x f₁' :=
  h' ▸ h

theorem HasMFDerivWithinAt.congr_of_eventuallyEq (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasMFDerivWithinAt I I' f₁ s x f' := by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin h₁
    apply Filter.mem_of_superset this fun y => _
    simp +contextual only [hx, mfld_simps]
  · simp only [hx, mfld_simps]

theorem HasMFDerivWithinAt.congr_mono (h : HasMFDerivWithinAt I I' f s x f')
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasMFDerivWithinAt I I' f₁ t x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt I I' f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt I I' f₁ x f' := by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ :)
  rwa [nhdsWithin_univ]

theorem mdifferentiableWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f₁ s x ↔ MDifferentiableWithinAt I I' f s x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff h₁ hx

theorem MDifferentiableWithinAt.congr_of_mem
    (h : MDifferentiableWithinAt I I' f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    MDifferentiableWithinAt I I' f₁ s x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem h h₁ hx

theorem mdifferentiableWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    MDifferentiableWithinAt I I' f₁ s x ↔ MDifferentiableWithinAt I I' f s x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem h₁ hx

theorem Filter.EventuallyEq.mdifferentiablefWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f₁ s x ↔ MDifferentiableWithinAt I I' f s x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDifferentiableWithinAt I I' f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt

theorem MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem
    (h : MDifferentiableWithinAt I I' f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    MDifferentiableWithinAt I I' f₁ s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

theorem MDifferentiableWithinAt.congr_of_eventuallyEq_insert
    (h : MDifferentiableWithinAt I I' f s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
    MDifferentiableWithinAt I I' f₁ s x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert x s)).of_insert

theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f₁ s x :=
  mdifferentiablefWithinAt_iff h₁.symm hx.symm

theorem MDifferentiableWithinAt.congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    MDifferentiableWithinAt I I' f₁ t x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt

theorem MDifferentiableWithinAt.congr (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

/-- Version of `MDifferentiableWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both. -/
theorem MDifferentiableWithinAt.congr' (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hst : s ⊆ t) (hxt : x ∈ t) : MDifferentiableWithinAt I I' f₁ s x :=
  h.congr (fun _y hy ↦ ht _y (hst hy)) (ht x hxt)

theorem Filter.EventuallyEq.mdifferentiableAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    MDifferentiableAt I I' f₁ x ↔ MDifferentiableAt I I' f x :=
  differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq h₁

theorem MDifferentiableOn.congr (h : MDifferentiableOn I I' f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
    MDifferentiableOn I I' f₁ s :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr h h₁

theorem mdifferentiableOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
    MDifferentiableOn I I' f₁ s ↔ MDifferentiableOn I I' f s :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff h₁

theorem MDifferentiableOn.congr_mono (h : MDifferentiableOn I I' f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : MDifferentiableOn I I' f₁ t := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDifferentiableAt I I' f x)
    (hL : f₁ =ᶠ[𝓝 x] f) : MDifferentiableAt I I' f₁ x :=
  (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt

theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f₁ t x = mfderivWithin I I' f s x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt

theorem MDifferentiableWithinAt.mfderivWithin_mono (h : MDifferentiableWithinAt I I' f s x)
    (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f t x = mfderivWithin I I' f s x :=
  h.mfderivWithin_congr_mono (fun _ _ ↦ rfl) rfl hxt h₁

theorem MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin
    (h : MDifferentiableWithinAt I I' f s x) (hxt : UniqueMDiffWithinAt I t x) (h₁ : s ∈ 𝓝[t] x) :
    mfderivWithin I I' f t x = mfderivWithin I I' f s x :=
  (HasMFDerivWithinAt.mono_of_mem_nhdsWithin h.hasMFDerivWithinAt h₁).mfderivWithin hxt

theorem Filter.EventuallyEq.mfderivWithin_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    mfderivWithin I I' f₁ s x = mfderivWithin I I' f s x := by
  by_cases h : MDifferentiableWithinAt I I' f s x
  · unfold mfderivWithin
    simp only [h, (hL.mdifferentiableWithinAt_iff hx).1 h, ↓reduceIte, writtenInExtChartAt]
    apply Filter.EventuallyEq.fderivWithin_eq; swap
    · simp [hx]
    filter_upwards [extChartAt_preimage_mem_nhdsWithin (I := I) hL] with y hy
    simp only [preimage_setOf_eq, mem_setOf_eq] at hy
    simp [-extChartAt, hy, hx]
  · unfold mfderivWithin
    rw [if_neg h, if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff hx]

theorem Filter.EventuallyEq.mfderivWithin_eq_of_mem (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    mfderivWithin I I' f₁ s x = mfderivWithin I I' f s x :=
  hL.mfderivWithin_eq (mem_of_mem_nhdsWithin hx hL :)

theorem mfderivWithin_congr (hL : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    mfderivWithin I I' f₁ s x = mfderivWithin I I' f s x :=
  Filter.EventuallyEq.mfderivWithin_eq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

theorem mfderivWithin_congr_of_mem (hL : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) :
    mfderivWithin I I' f₁ s x = mfderivWithin I I' f s x :=
  Filter.EventuallyEq.mfderivWithin_eq_of_mem (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

theorem tangentMapWithin_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f₁ s p := by
  refine TotalSpace.ext (h p.1 hp) ?_
  rw [tangentMapWithin, h p.1 hp, tangentMapWithin, mfderivWithin_congr h (h _ hp)]

theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
    mfderiv I I' f₁ x = mfderiv I I' f x := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL :)
  rw [← mfderivWithin_univ, ← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq A

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') := by subst h; rfl

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr {f' : M → M'} (h : f = f') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) := by subst h; rfl

/-! ### Composition lemmas -/

variable (x)

theorem HasMFDerivWithinAt.comp (hg : HasMFDerivWithinAt I' I'' g u (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') (hst : s ⊆ f ⁻¹' u) :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this, ← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

/-- The **chain rule for manifolds**. -/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') :
    HasMFDerivAt I I'' (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt I' I'' g (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

theorem MDifferentiableWithinAt.comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivWithinAt I I' f s x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivWithinAt I' I'' g u (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt

theorem MDifferentiableWithinAt.comp_of_eq {y : M'} (hg : MDifferentiableWithinAt I' I'' g u y)
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hy : f x = y) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  subst hy; exact hg.comp _ hf h

theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
    (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : f ⁻¹' u ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x :=
  (hg.comp _ (hf.mono inter_subset_right) inter_subset_left).mono_of_mem_nhdsWithin
    (Filter.inter_mem h self_mem_nhdsWithin)

theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {y : M'}
    (hg : MDifferentiableWithinAt I' I'' g u y)
    (hf : MDifferentiableWithinAt I I' f s x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hy : f x = y) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  subst hy; exact MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin _ hg hf h

theorem MDifferentiableAt.comp (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) : MDifferentiableAt I I'' (g ∘ f) x :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableAt.comp_of_eq {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) : MDifferentiableAt I I'' (g ∘ f) x := by
  subst hy; exact hg.comp _ hf

theorem MDifferentiableAt.comp_mdifferentiableWithinAt
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableWithinAt I I' f s x) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rw [← mdifferentiableWithinAt_univ] at hg
  exact hg.comp _ hf (by simp)

theorem MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq {y : M'}
    (hg : MDifferentiableAt I' I'' g y) (hf : MDifferentiableWithinAt I I' f s x) (hy : f x = y) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  subst hy; exact hg.comp_mdifferentiableWithinAt _ hf

theorem mfderivWithin_comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h

theorem mfderivWithin_comp_of_eq {x : M} {y : M'} (hg : MDifferentiableWithinAt I' I'' g u y)
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffWithinAt I s x)
    (hy : f x = y) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u y).comp (mfderivWithin I I' f s x) := by
  subst hy; exact mfderivWithin_comp x hg hf h hxs

theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin
    (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : f ⁻¹' u ∈ 𝓝[s] x)
    (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) := by
  have A : s ∩ f ⁻¹' u ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin h
  have B : mfderivWithin I I'' (g ∘ f) s x = mfderivWithin I I'' (g ∘ f) (s ∩ f ⁻¹' u) x := by
    apply MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin _ hxs A
    exact hg.comp _ (hf.mono inter_subset_left) inter_subset_right
  have C : mfderivWithin I I' f s x = mfderivWithin I I' f (s ∩ f ⁻¹' u) x :=
    MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (hf.mono inter_subset_left) hxs A
  rw [B, C]
  exact mfderivWithin_comp _ hg (hf.mono inter_subset_left) inter_subset_right (hxs.inter' h)

theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq {y : M'}
    (hg : MDifferentiableWithinAt I' I'' g u y)
    (hf : MDifferentiableWithinAt I I' f s x) (h : f ⁻¹' u ∈ 𝓝[s] x)
    (hxs : UniqueMDiffWithinAt I s x) (hy : f x = y) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u y).comp (mfderivWithin I I' f s x) := by
  subst hy; exact mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hg hf h hxs

theorem mfderiv_comp_mfderivWithin (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderiv I' I'' g (f x)).comp (mfderivWithin I I' f s x) := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_comp _ hg.mdifferentiableWithinAt hf (by simp) hxs

theorem mfderiv_comp_mfderivWithin_of_eq {x : M} {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableWithinAt I I' f s x) (hxs : UniqueMDiffWithinAt I s x) (hy : f x = y) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderiv I' I'' g y).comp (mfderivWithin I I' f s x) := by
  subst hy; exact mfderiv_comp_mfderivWithin x hg hf hxs

theorem mfderiv_comp (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt

theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  subst hy; exact mfderiv_comp x hg hf

theorem mfderiv_comp_apply (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) (v : TangentSpace I x) :
    mfderiv I I'' (g ∘ f) x v = (mfderiv I' I'' g (f x)) ((mfderiv I I' f x) v) := by
  rw [mfderiv_comp _ hg hf]
  rfl

theorem mfderiv_comp_apply_of_eq {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) (v : TangentSpace I x) :
    mfderiv I I'' (g ∘ f) x v = (mfderiv I' I'' g y) ((mfderiv I I' f x) v) := by
  subst hy; exact mfderiv_comp_apply _ hg hf v

theorem MDifferentiableOn.comp (hg : MDifferentiableOn I' I'' g u) (hf : MDifferentiableOn I I' f s)
    (st : s ⊆ f ⁻¹' u) : MDifferentiableOn I I'' (g ∘ f) s := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

theorem MDifferentiable.comp_mdifferentiableOn (hg : MDifferentiable I' I'' g)
    (hf : MDifferentiableOn I I' f s) : MDifferentiableOn I I'' (g ∘ f) s := by
  rw [← mdifferentiableOn_univ] at hg
  exact hg.comp hf (by simp)

theorem MDifferentiable.comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    MDifferentiable I I'' (g ∘ f) := fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)

theorem tangentMapWithin_comp_at (p : TangentBundle I M)
    (hg : MDifferentiableWithinAt I' I'' g u (f p.1)) (hf : MDifferentiableWithinAt I I' f s p.1)
    (h : s ⊆ f ⁻¹' u) (hps : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I'' (g ∘ f) s p =
      tangentMapWithin I' I'' g u (tangentMapWithin I I' f s p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl

theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDifferentiableAt I' I'' g (f p.1))
    (hf : MDifferentiableAt I I' f p.1) :
    tangentMap I I'' (g ∘ f) p = tangentMap I' I'' g (tangentMap I I' f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl

theorem tangentMap_comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    tangentMap I I'' (g ∘ f) = tangentMap I' I'' g ∘ tangentMap I I' f := by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

end DerivativesProperties
