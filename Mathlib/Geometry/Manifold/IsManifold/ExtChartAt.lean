/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Extended charts in smooth manifolds

In a `C^n` manifold with corners with the model `I` on `(E, H)`, the charts take values in the
model space `H`. However, we also need to use extended charts taking values in the model vector
space `E`. These extended charts are not `OpenPartialHomeomorph` as the target is not open in `E`
in general, but we can still register them as `PartialEquiv`s.

## Main definitions

* `OpenPartialHomeomorph.extend`: compose an open partial homeomorphism into `H` with the model `I`,
  to obtain a `PartialEquiv` into `E`. Extended charts are an example of this.
* `extChartAt I x`: the extended chart at `x`, obtained by composing the `chartAt H x` with `I`.
  Since the target is in general not open, this is not an open partial homeomorphism in general, but
  we register them as `PartialEquiv`s.
* `I.extendCoordChange e e'`: the change of extended charts `(e.extend I).symm ≫ e'.extend I`.

## Main results

* `ModelWithCorners.contDiffOn_extendCoordChange`: if `f` and `f'` lie in the maximal atlas on `M`,
  `I.extendCoordChange f f'` is Cⁿ on its source

* `contDiffOn_ext_coord_change`: for `x x' : M`, the coordinate change
  `(extChartAt I x').symm ≫ extChartAt I x` is continuous on its source

* `Manifold.locallyCompact_of_finiteDimensional`: a finite-dimensional manifold
  modelled on a locally compact field (such as ℝ, ℂ or the `p`-adic numbers) is locally compact
* `LocallyCompactSpace.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a locally compact space.
* `FiniteDimensional.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a finite-dimensional space

-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology

variable {𝕜 E M H E' M' H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {n : WithTop ℕ∞}
  (f f' : OpenPartialHomeomorph M H)
  {I : ModelWithCorners 𝕜 E H} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] {I' : ModelWithCorners 𝕜 E' H'} {s t : Set M}

section ExtendedCharts

namespace OpenPartialHomeomorph

variable (I) in
/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps]
def extend : PartialEquiv M E :=
  f.toPartialEquiv ≫ I.toPartialEquiv

theorem extend_coe : ⇑(f.extend I) = I ∘ f :=
  rfl

theorem extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm :=
  rfl

theorem extend_source : (f.extend I).source = f.source := by
  rw [extend, PartialEquiv.trans_source, I.source_eq, preimage_univ, inter_univ]

theorem isOpen_extend_source : IsOpen (f.extend I).source := by
  rw [extend_source]
  exact f.open_source

theorem extend_target : (f.extend I).target = I.symm ⁻¹' f.target ∩ range I := by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]

theorem extend_target' : (f.extend I).target = I '' f.target := by
  rw [extend, PartialEquiv.trans_target'', I.source_eq, univ_inter, I.toPartialEquiv_coe]

lemma isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target := by
  rw [extend_target, I.range_eq_univ, inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

theorem mapsTo_extend (hs : s ⊆ f.source) :
    MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s ∩ range I) := by
  rw [mapsTo_iff_image_subset, extend_coe, extend_coe_symm, preimage_comp, ← I.image_eq, image_comp,
    f.image_eq_target_inter_inv_preimage hs]
  exact image_mono inter_subset_right

theorem extend_left_inv {x : M} (hxf : x ∈ f.source) : (f.extend I).symm (f.extend I x) = x :=
  (f.extend I).left_inv <| by rwa [f.extend_source]

/-- Variant of `f.extend_left_inv I`, stated in terms of images. -/
lemma extend_left_inv' (ht : t ⊆ f.source) : ((f.extend I).symm ∘ (f.extend I)) '' t = t :=
  EqOn.image_eq_self (fun _ hx ↦ f.extend_left_inv (ht hx))

theorem extend_source_mem_nhds {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝 x :=
  (isOpen_extend_source f).mem_nhds <| by rwa [f.extend_source]

theorem extend_source_mem_nhdsWithin {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds <| extend_source_mem_nhds f h

theorem continuousOn_extend : ContinuousOn (f.extend I) (f.extend I).source := by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn

theorem continuousAt_extend {x : M} (h : x ∈ f.source) : ContinuousAt (f.extend I) x :=
  (continuousOn_extend f).continuousAt <| extend_source_mem_nhds f h

theorem map_extend_nhds {x : M} (hy : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x := by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]

theorem map_extend_nhds_of_mem_interior_range {x : M} (hx : x ∈ f.source)
    (h'x : f.extend I x ∈ interior (range I)) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx, nhdsWithin_eq_nhds]
  exact mem_of_superset (isOpen_interior.mem_nhds h'x) interior_subset

theorem map_extend_nhds_of_boundaryless [I.Boundaryless] {x : M} (hx : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx, I.range_eq_univ, nhdsWithin_univ]

theorem extend_target_mem_nhdsWithin {y : M} (hy : y ∈ f.source) :
    (f.extend I).target ∈ 𝓝[range I] f.extend I y := by
  rw [← PartialEquiv.image_source_eq_target, ← map_extend_nhds f hy]
  exact image_mem_map (extend_source_mem_nhds _ hy)

lemma extend_image_target_mem_nhds {x : M} (hx : x ∈ f.source) :
    I '' f.target ∈ 𝓝[range I] (f.extend I) x := by
  rw [← f.map_extend_nhds hx, Filter.mem_map,
    f.extend_coe, Set.preimage_comp, I.preimage_image f.target]
  exact (f.continuousAt hx).preimage_mem_nhds (f.open_target.mem_nhds (f.map_source hx))

theorem extend_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x ∈ f.source)
    {s : Set M} (h : s ∈ 𝓝 x) : (f.extend I) '' s ∈ 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_boundaryless hx, Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

theorem extend_image_nhds_mem_nhds_of_mem_interior_range {x} (hx : x ∈ f.source)
    (h'x : f.extend I x ∈ interior (range I)) {s : Set M} (h : s ∈ 𝓝 x) :
    (f.extend I) '' s ∈ 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_mem_interior_range hx h'x, Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s

theorem extend_target_subset_range : (f.extend I).target ⊆ range I := by simp only [mfld_simps]

lemma interior_extend_target_subset_interior_range :
    interior (f.extend I).target ⊆ interior (range I) := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right

/-- If `y ∈ f.target` and `I y ∈ interior (range I)`,
then `I y` is an interior point of `(I ∘ f).target`. -/
lemma mem_interior_extend_target {y : H} (hy : y ∈ f.target)
    (hy' : I y ∈ interior (range I)) : I y ∈ interior (f.extend I).target := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq,
    mem_inter_iff, mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

theorem nhdsWithin_extend_target_eq {y : M} (hy : y ∈ f.source) :
    𝓝[(f.extend I).target] f.extend I y = 𝓝[range I] f.extend I y :=
  (nhdsWithin_mono _ (extend_target_subset_range _)).antisymm <|
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ hy)

theorem extend_target_eventuallyEq {y : M} (hy : y ∈ f.source) :
    (f.extend I).target =ᶠ[𝓝 (f.extend I y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extend_target_eq _ hy)

theorem continuousAt_extend_symm' {x : E} (h : x ∈ (f.extend I).target) :
    ContinuousAt (f.extend I).symm x :=
  (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt

theorem continuousAt_extend_symm {x : M} (h : x ∈ f.source) :
    ContinuousAt (f.extend I).symm (f.extend I x) :=
  continuousAt_extend_symm' f <| (f.extend I).map_source <| by rwa [f.extend_source]

theorem continuousOn_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).target := fun _ h =>
  (continuousAt_extend_symm' _ h).continuousWithinAt

theorem extend_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M → X}
    {s : Set M} {x : M} :
    ContinuousWithinAt (g ∘ (f.extend I).symm) ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I x) ↔
      ContinuousWithinAt (g ∘ f.symm) (f.symm ⁻¹' s) (f x) := by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl

theorem isOpen_extend_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((f.extend I).source ∩ f.extend I ⁻¹' s) :=
  (continuousOn_extend f).isOpen_inter_preimage (isOpen_extend_source _) hs

theorem isOpen_extend_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen (f.source ∩ f.extend I ⁻¹' s) := by
  rw [← extend_source f (I := I)]; exact isOpen_extend_preimage' f hs

theorem map_extend_nhdsWithin_eq_image {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source ∩ s)] f.extend I y := by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f hy)).symm
    _ = 𝓝[e '' (e.source ∩ s)] e y :=
      ((f.extend I).leftInvOn.mono inter_subset_left).map_nhdsWithin_eq
        ((f.extend I).left_inv <| by rwa [f.extend_source])
        (continuousAt_extend_symm f hy).continuousWithinAt
        (continuousAt_extend f hy).continuousWithinAt

theorem map_extend_nhdsWithin_eq_image_of_subset {y : M} (hy : y ∈ f.source) (hs : s ⊆ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' s] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image _ hy, inter_eq_self_of_subset_right]
  rwa [extend_source]

theorem map_extend_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image f hy, nhdsWithin_inter, ←
    nhdsWithin_extend_target_eq _ hy, ← nhdsWithin_inter, (f.extend I).image_source_inter_eq',
    inter_comm]

theorem map_extend_symm_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y) = 𝓝[s] y := by
  rw [← map_extend_nhdsWithin f hy, map_map, Filter.map_congr, map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ hy)

theorem map_extend_symm_nhdsWithin_range {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[range I] f.extend I y) = 𝓝 y := by
  rw [← nhdsWithin_univ, ← map_extend_symm_nhdsWithin f (I := I) hy, preimage_univ, univ_inter]

theorem tendsto_extend_comp_iff {α : Type*} {l : Filter α} {g : α → M}
    (hg : ∀ᶠ z in l, g z ∈ f.source) {y : M} (hy : y ∈ f.source) :
    Tendsto (f.extend I ∘ g) l (𝓝 (f.extend I y)) ↔ Tendsto g l (𝓝 y) := by
  refine ⟨fun h u hu ↦ mem_map.2 ?_, (continuousAt_extend _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm hy).tendsto.comp h
  rw [extend_left_inv _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ hz, mem_preimage] using hzu

-- there is no definition `writtenInExtend` but we already use some made-up names in this file
theorem continuousWithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M → M'}
    {y : M} (hy : y ∈ f.source) (hgy : g y ∈ f'.source) (hmaps : MapsTo g s f'.source) :
    ContinuousWithinAt (f'.extend I' ∘ g ∘ (f.extend I).symm)
      ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I y) ↔ ContinuousWithinAt g s y := by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ hy, f'.tendsto_extend_comp_iff _ hgy,
    ← f.map_extend_symm_nhdsWithin (I := I) hy, tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin (I := I) hy, eventually_map]
  filter_upwards [inter_mem_nhdsWithin _ (f.open_source.mem_nhds hy)] with z hz
  rw [comp_apply, extend_left_inv _ hz.2]
  exact hmaps hz.1

-- there is no definition `writtenInExtend` but we already use some made-up names in this file

/-- If `s ⊆ f.source` and `g x ∈ f'.source` whenever `x ∈ s`, then `g` is continuous on `s` if and
only if `g` written in charts `f.extend I` and `f'.extend I'` is continuous on `f.extend I '' s`. -/
theorem continuousOn_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M → M'}
    (hs : s ⊆ f.source) (hmaps : MapsTo g s f'.source) :
    ContinuousOn (f'.extend I' ∘ g ∘ (f.extend I).symm) (f.extend I '' s) ↔ ContinuousOn g s := by
  refine forall_mem_image.trans <| forall₂_congr fun x hx ↦ ?_
  refine (continuousWithinAt_congr_set ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← map_extend_nhdsWithin_eq_image_of_subset,
    ← map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]

theorem extend_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x : M} (hx : x ∈ f.source)
    (hs : s ∈ 𝓝[range I] (f.extend I x)) :
    (f.extend I) ⁻¹' s ∈ 𝓝 x := by
  rwa [← map_extend_nhds (I := I) f hx] at hs

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem extend_preimage_mem_nhdsWithin {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝[s] x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I x := by
  rwa [← map_extend_symm_nhdsWithin f (I := I) h, mem_map] at ht

theorem extend_preimage_mem_nhds {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝 x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝 (f.extend I x) := by
  apply (continuousAt_extend_symm f h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem extend_preimage_inter_eq :
    (f.extend I).symm ⁻¹' (s ∩ t) ∩ range I =
      (f.extend I).symm ⁻¹' s ∩ range I ∩ (f.extend I).symm ⁻¹' t := by
  mfld_set_tac

@[deprecated "Removed without replacement" (since := "2025-08-27")]
theorem extend_symm_preimage_inter_range_eventuallyEq_aux {s : Set M} {x : M} (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)]
      ((f.extend I).target ∩ (f.extend I).symm ⁻¹' s : Set _) := by
  rw [f.extend_target, inter_assoc, inter_comm (range I)]
  conv =>
    congr
    · skip
    rw [← univ_inter (_ ∩ range I)]
  refine (eventuallyEq_univ.mpr ?_).symm.inter EventuallyEq.rfl
  refine I.continuousAt_symm.preimage_mem_nhds (f.open_target.mem_nhds ?_)
  simp_rw [f.extend_coe, Function.comp_apply, I.left_inv, f.mapsTo hx]

theorem extend_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s ⊆ f.source)
    (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s := by
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← map_extend_nhdsWithin _ hx,
    map_extend_nhdsWithin_eq_image_of_subset _ hx hs]

lemma extend_prod (f' : OpenPartialHomeomorph M' H') :
    (f.prod f').extend (I.prod I') = (f.extend I).prod (f'.extend I') := by simp

end OpenPartialHomeomorph

namespace ModelWithCorners

/-- The change of charts from `e` to `e'` in the model vector space `E`. -/
abbrev extendCoordChange (e e' : OpenPartialHomeomorph M H) : PartialEquiv E E :=
  (e.extend I).symm ≫ e'.extend I

variable {e e' : OpenPartialHomeomorph M H}

lemma extendCoordChange_symm : (I.extendCoordChange e e').symm = I.extendCoordChange e' e := by
  rfl

lemma extendCoordChange_source :
    (I.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source := by
  simp_rw [extendCoordChange, PartialEquiv.trans_source, I.image_eq, e'.extend_source,
    PartialEquiv.symm_source, e.extend_target, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]

lemma extendCoordChange_target :
    (I.extendCoordChange e e').target = I '' (e.symm ≫ₕ e').target := by
  rw [← PartialEquiv.symm_source, ← OpenPartialHomeomorph.symm_source]
  exact I.extendCoordChange_source

lemma _root_.OpenPartialHomeomorph.extend_image_source_inter :
    f.extend I '' (f.source ∩ f'.source) = (I.extendCoordChange f f').source := by
  simp_rw [I.extendCoordChange_source, f.extend_coe, image_comp I f,
    OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target]

lemma extendCoordChange_source_mem_nhdsWithin {x : E}
    (hx : x ∈ (I.extendCoordChange e e').source) :
    (I.extendCoordChange e e').source ∈ 𝓝[range I] x := by
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (OpenPartialHomeomorph.open_source _).mem_nhds hx

lemma extendCoordChange_source_mem_nhdsWithin' {x : M} (hxe : x ∈ e.source)
    (hxe' : x ∈ e'.source) :
    (I.extendCoordChange e e').source ∈ 𝓝[range I] e.extend I x := by
  apply extendCoordChange_source_mem_nhdsWithin
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

lemma uniqueDiffOn_extendCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChange e e').source := by
  rw [extendCoordChange_source, I.image_eq]
  exact I.uniqueDiffOn_preimage <| e.isOpen_inter_preimage_symm e'.open_source

lemma uniqueDiffOn_extendCoordChange_target : UniqueDiffOn 𝕜 (I.extendCoordChange e e').target := by
  rw [← extendCoordChange_symm, PartialEquiv.symm_target]
  exact uniqueDiffOn_extendCoordChange_source

open IsManifold

variable [ChartedSpace H M]

lemma contDiffOn_extendCoordChange (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e') (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas he he').1

lemma contDiffWithinAt_extendCoordChange (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) {x : E} (hx : x ∈ (I.extendCoordChange e e').source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) x := by
  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((OpenPartialHomeomorph.open_source _).mem_nhds hz)

lemma contDiffWithinAt_extendCoordChange' (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) {x : M} (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) (e.extend I x) := by
  refine I.contDiffWithinAt_extendCoordChange he he' ?_
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩

lemma contDiffOn_extendCoordChange_symm (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e').symm (I.extendCoordChange e e').target :=
  I.contDiffOn_extendCoordChange he' he

lemma isInvertible_fderivWithin_extendCoordChange (hn : n ≠ 0)
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M)
    {x : E} (hx : x ∈ (I.extendCoordChange e e').source) :
    ContinuousLinearMap.IsInvertible <|
      fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source x := by
  set φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  refine .of_inverse (g := (fderivWithin 𝕜 φ.symm φ.target (φ x))) ?_ ?_
  · rw [← φ.left_inv hx, φ.right_inv (φ.map_source hx), ← fderivWithin_comp,
      fderivWithin_congr' φ.rightInvOn.eqOn (φ.map_source hx), fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
    · exact (φ.left_inv hx ▸ ((hφ _ hx).differentiableWithinAt hn) :)
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact φ.symm_mapsTo
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
  · rw [← fderivWithin_comp, fderivWithin_congr' φ.leftInvOn.eqOn hx, fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact (hφ _ hx).differentiableWithinAt hn
    · exact φ.mapsTo
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx

end ModelWithCorners

namespace OpenPartialHomeomorph

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source := ModelWithCorners.extendCoordChange_source

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin' :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'

@[deprecated (since := "2026-02-16")]
alias contDiffOn_extend_coord_change := ModelWithCorners.contDiffOn_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change := ModelWithCorners.contDiffWithinAt_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change' := ModelWithCorners.contDiffWithinAt_extendCoordChange'

end OpenPartialHomeomorph

open OpenPartialHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

variable (I) in
/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
def extChartAt (x : M) : PartialEquiv M E :=
  (chartAt H x).extend I

theorem extChartAt_coe (x : M) : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl

theorem extChartAt_coe_symm (x : M) : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl

variable (I) in
theorem extChartAt_source (x : M) : (extChartAt I x).source = (chartAt H x).source :=
  extend_source _

theorem isOpen_extChartAt_source (x : M) : IsOpen (extChartAt I x).source :=
  isOpen_extend_source _

theorem mem_extChartAt_source (x : M) : x ∈ (extChartAt I x).source := by
  simp only [extChartAt_source, mem_chart_source]

theorem mem_extChartAt_target (x : M) : extChartAt I x x ∈ (extChartAt I x).target :=
  (extChartAt I x).map_source <| mem_extChartAt_source _

variable (I) in
theorem extChartAt_target (x : M) :
    (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target ∩ range I :=
  extend_target _

theorem uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn 𝕜 (extChartAt I x).target := by
  rw [extChartAt_target]
  exact I.uniqueDiffOn_preimage (chartAt H x).open_target

theorem uniqueDiffWithinAt_extChartAt_target (x : M) :
    UniqueDiffWithinAt 𝕜 (extChartAt I x).target (extChartAt I x x) :=
  uniqueDiffOn_extChartAt_target x _ <| mem_extChartAt_target x

theorem extChartAt_to_inv (x : M) : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_extChartAt_source x)

theorem mapsTo_extChartAt {x : M} (hs : s ⊆ (chartAt H x).source) :
    MapsTo (extChartAt I x) s ((extChartAt I x).symm ⁻¹' s ∩ range I) :=
  mapsTo_extend _ hs

theorem extChartAt_source_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝 x' :=
  extend_source_mem_nhds _ <| by rwa [← extChartAt_source I]

theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source ∈ 𝓝 x :=
  extChartAt_source_mem_nhds' (mem_extChartAt_source x)

theorem extChartAt_source_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝[s] x' :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' h)

theorem extChartAt_source_mem_nhdsWithin (x : M) : (extChartAt I x).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)

theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
  continuousOn_extend _

theorem continuousAt_extChartAt' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x) x' :=
  continuousAt_extend _ <| by rwa [← extChartAt_source I]

theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
  continuousAt_extChartAt' (mem_extChartAt_source x)

theorem map_extChartAt_nhds' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y :=
  map_extend_nhds _ <| by rwa [← extChartAt_source I]

theorem map_extChartAt_nhds (x : M) : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x :=
  map_extChartAt_nhds' <| mem_extChartAt_source x

theorem map_extChartAt_nhds_of_boundaryless [I.Boundaryless] (x : M) :
    map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) (mem_chart_source H x)

theorem extChartAt_image_nhds_mem_nhds_of_mem_interior_range {x y}
    (hx : y ∈ (extChartAt I x).source)
    (h'x : extChartAt I x y ∈ interior (range I)) {s : Set M} (h : s ∈ 𝓝 y) :
    (extChartAt I x) '' s ∈ 𝓝 (extChartAt I x y) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_mem_interior_range _ (by simpa using hx) h'x h

variable {x} in
theorem extChartAt_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless]
    {x : M} (hx : s ∈ 𝓝 x) : extChartAt I x '' s ∈ 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_boundaryless _ (mem_chart_source H x) hx

theorem extChartAt_target_mem_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x y :=
  extend_target_mem_nhdsWithin _ <| by rwa [← extChartAt_source I]

theorem extChartAt_target_mem_nhdsWithin (x : M) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x x :=
  extChartAt_target_mem_nhdsWithin' (mem_extChartAt_source x)

theorem extChartAt_target_mem_nhdsWithin_of_mem {x : M} {y : E} (hy : y ∈ (extChartAt I x).target) :
    (extChartAt I x).target ∈ 𝓝[range I] y := by
  rw [← (extChartAt I x).right_inv hy]
  apply extChartAt_target_mem_nhdsWithin'
  exact (extChartAt I x).map_target hy

theorem extChartAt_target_union_compl_range_mem_nhds_of_mem {y : E} {x : M}
    (hy : y ∈ (extChartAt I x).target) : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 y := by
  rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
  exact Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin_of_mem hy) self_mem_nhdsWithin

/-- If we're boundaryless, `extChartAt` has open target -/
theorem isOpen_extChartAt_target [I.Boundaryless] (x : M) : IsOpen (extChartAt I x).target := by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (OpenPartialHomeomorph.open_target _).preimage I.continuous_symm

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of the key point -/
theorem extChartAt_target_mem_nhds [I.Boundaryless] (x : M) :
    (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := by
  convert extChartAt_target_mem_nhdsWithin x
  simp only [I.range_eq_univ, nhdsWithin_univ]

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of any of its points -/
theorem extChartAt_target_mem_nhds' [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) : (extChartAt I x).target ∈ 𝓝 y :=
  (isOpen_extChartAt_target x).mem_nhds m

theorem extChartAt_target_subset_range (x : M) : (extChartAt I x).target ⊆ range I := by
  simp only [mfld_simps]

/-- Around the image of a point in the source, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`. -/
theorem nhdsWithin_extChartAt_target_eq' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y :=
  nhdsWithin_extend_target_eq _ <| by rwa [← extChartAt_source I]

/-- Around a point in the target, the neighborhoods are the same within `(extChartAt I x).target`
and within `range I`. -/
theorem nhdsWithin_extChartAt_target_eq_of_mem {x : M} {z : E} (hz : z ∈ (extChartAt I x).target) :
    𝓝[(extChartAt I x).target] z = 𝓝[range I] z := by
  rw [← PartialEquiv.right_inv (extChartAt I x) hz]
  exact nhdsWithin_extChartAt_target_eq' ((extChartAt I x).map_target hz)

/-- Around the image of the base point, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`. -/
theorem nhdsWithin_extChartAt_target_eq (x : M) :
    𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x :=
  nhdsWithin_extChartAt_target_eq' (mem_extChartAt_source x)

/-- Around the image of a point in the source, `(extChartAt I x).target` and `range I`
coincide locally. -/
theorem extChartAt_target_eventuallyEq' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq' hy)

/-- Around a point in the target, `(extChartAt I x).target` and `range I` coincide locally. -/
theorem extChartAt_target_eventuallyEq_of_mem {x : M} {z : E} (hz : z ∈ (extChartAt I x).target) :
    (extChartAt I x).target =ᶠ[𝓝 z] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq_of_mem hz)

/-- Around the image of the base point, `(extChartAt I x).target` and `range I` coincide locally. -/
theorem extChartAt_target_eventuallyEq {x : M} :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x x)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq x)

theorem continuousAt_extChartAt_symm'' {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    ContinuousAt (extChartAt I x).symm y :=
  continuousAt_extend_symm' _ h

theorem continuousAt_extChartAt_symm' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
  continuousAt_extChartAt_symm'' <| (extChartAt I x).map_source h

theorem continuousAt_extChartAt_symm (x : M) :
    ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  continuousAt_extChartAt_symm' (mem_extChartAt_source x)

theorem continuousOn_extChartAt_symm (x : M) :
    ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
  fun _y hy => (continuousAt_extChartAt_symm'' hy).continuousWithinAt

lemma extChartAt_target_subset_closure_interior {x : M} :
    (extChartAt I x).target ⊆ closure (interior (extChartAt I x).target) := by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have A : t ∩ ((extChartAt I x).target ∪ (range I)ᶜ) ∈ 𝓝 y :=
    inter_mem ht (extChartAt_target_union_compl_range_mem_nhds_of_mem hy)
  have B : y ∈ closure (interior (range I)) := by
    apply I.range_subset_closure_interior (extChartAt_target_subset_range x hy)
  obtain ⟨z, ⟨tz, h'z⟩, hz⟩ :
      (t ∩ ((extChartAt I x).target ∪ (range ↑I)ᶜ) ∩ interior (range I)).Nonempty :=
    mem_closure_iff_nhds.1 B _ A
  refine ⟨z, ⟨tz, ?_⟩⟩
  have h''z : z ∈ (extChartAt I x).target := by simpa [interior_subset hz] using h'z
  exact (extChartAt_target_eventuallyEq_of_mem h''z).symm.mem_interior hz

variable (I) in
theorem interior_extChartAt_target_nonempty (x : M) :
    (interior (extChartAt I x).target).Nonempty := by
  by_contra! H
  have := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  simp only [H, closure_empty, mem_empty_iff_false] at this

lemma extChartAt_mem_closure_interior {x₀ x : M}
    (hx : x ∈ closure (interior s)) (h'x : x ∈ (extChartAt I x₀).source) :
    extChartAt I x₀ x ∈
      closure (interior ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target)) := by
  simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
  intro o o_open ho
  obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
      ((extChartAt I x₀) ⁻¹' o ∩ (extChartAt I x₀).source ∩ interior s).Nonempty := by
    have : (extChartAt I x₀) ⁻¹' o ∈ 𝓝 x := by
      apply (continuousAt_extChartAt' h'x).preimage_mem_nhds (o_open.mem_nhds ho)
    refine (mem_closure_iff_nhds.1 hx) _ (inter_mem this ?_)
    apply (isOpen_extChartAt_source x₀).mem_nhds h'x
  have A : interior (↑(extChartAt I x₀).symm ⁻¹' s) ∈ 𝓝 (extChartAt I x₀ y) := by
    simp only [interior_mem_nhds]
    apply (continuousAt_extChartAt_symm' hy).preimage_mem_nhds
    simp only [hy, PartialEquiv.left_inv]
    exact mem_interior_iff_mem_nhds.mp ys
  have B : (extChartAt I x₀) y ∈ closure (interior (extChartAt I x₀).target) := by
    apply extChartAt_target_subset_closure_interior (x := x₀)
    exact (extChartAt I x₀).map_source hy
  exact mem_closure_iff_nhds.1 B _ (inter_mem (o_open.mem_nhds yo) A)

theorem isOpen_extChartAt_preimage' (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).source ∩ extChartAt I x ⁻¹' s) :=
  isOpen_extend_preimage' _ hs

theorem isOpen_extChartAt_preimage (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).source ∩ extChartAt I x ⁻¹' s) := by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' x hs

theorem map_extChartAt_nhdsWithin_eq_image' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x y :=
  map_extend_nhdsWithin_eq_image _ <| by rwa [← extChartAt_source I]

theorem map_extChartAt_nhdsWithin_eq_image (x : M) :
    map (extChartAt I x) (𝓝[s] x) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x x :=
  map_extChartAt_nhdsWithin_eq_image' (mem_extChartAt_source x)

theorem map_extChartAt_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y :=
  map_extend_nhdsWithin _ <| by rwa [← extChartAt_source I]

theorem map_extChartAt_nhdsWithin (x : M) :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x :=
  map_extChartAt_nhdsWithin' (mem_extChartAt_source x)

theorem map_extChartAt_symm_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y) =
      𝓝[s] y :=
  map_extend_symm_nhdsWithin _ <| by rwa [← extChartAt_source I]

theorem map_extChartAt_symm_nhdsWithin_range' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y :=
  map_extend_symm_nhdsWithin_range _ <| by rwa [← extChartAt_source I]

theorem map_extChartAt_symm_nhdsWithin (x : M) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x) =
      𝓝[s] x :=
  map_extChartAt_symm_nhdsWithin' (mem_extChartAt_source x)

theorem map_extChartAt_symm_nhdsWithin_range (x : M) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x :=
  map_extChartAt_symm_nhdsWithin_range' (mem_extChartAt_source x)

theorem extChartAt_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x x' : M}
    (hx : x' ∈ (extChartAt I x).source)
    (hs : s ∈ 𝓝[range I] (extChartAt I x x')) :
    (extChartAt I x) ⁻¹' s ∈ 𝓝 x' :=
  extend_preimage_mem_nhds_of_mem_nhdsWithin _ (by simpa using hx) hs

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem extChartAt_preimage_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x' := by
  rwa [← map_extChartAt_symm_nhdsWithin' h, mem_map] at ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
theorem extChartAt_preimage_mem_nhdsWithin {x : M} (ht : t ∈ 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  extChartAt_preimage_mem_nhdsWithin' (mem_extChartAt_source x) ht

theorem extChartAt_preimage_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝 x') : (extChartAt I x).symm ⁻¹' t ∈ 𝓝 (extChartAt I x x') :=
  extend_preimage_mem_nhds _ (by rwa [← extChartAt_source I]) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
theorem extChartAt_preimage_mem_nhds {x : M} (ht : t ∈ 𝓝 x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝 ((extChartAt I x) x) := by
  apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _)]

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem extChartAt_preimage_inter_eq (x : M) :
    (extChartAt I x).symm ⁻¹' (s ∩ t) ∩ range I =
      (extChartAt I x).symm ⁻¹' s ∩ range I ∩ (extChartAt I x).symm ⁻¹' t := by
  mfld_set_tac

theorem ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
    {f : M → M'} {x : M} (hc : ContinuousWithinAt f s x) :
    𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x) =
      𝓝[(extChartAt I x).target ∩
        (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source)] (extChartAt I x x) := by
  rw [← (extChartAt I x).image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image,
    ← map_extChartAt_nhdsWithin, nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _)

theorem ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
    {f : M → M'} {x : M} (hc : ContinuousWithinAt f s x) :
    ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E) =ᶠ[𝓝 (extChartAt I x x)]
      ((extChartAt I x).target ∩
        (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source) : Set E) := by
  rw [← nhdsWithin_eq_iff_eventuallyEq]
  exact hc.nhdsWithin_extChartAt_symm_preimage_inter_range

/-! We use the name `ext_coord_change` for `(extChartAt I x').symm ≫ extChartAt I x`. -/

theorem ext_coord_change_source (x x' : M) :
    ((extChartAt I x').symm ≫ extChartAt I x).source =
      I '' ((chartAt H x').symm ≫ₕ chartAt H x).source :=
  I.extendCoordChange_source

open IsManifold

theorem contDiffOn_ext_coord_change [IsManifold I n M] (x x' : M) :
    ContDiffOn 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)

theorem contDiffWithinAt_ext_coord_change [IsManifold I n M] (x x' : M) {y : E}
    (hy : y ∈ ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffWithinAt 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm) (range I) y :=
  I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy

variable (I I') in
/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps]
def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm

set_option backward.isDefEq.respectTransparency false in
theorem writtenInExtChartAt_chartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I x (chartAt H x) y = y := by simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
theorem writtenInExtChartAt_chartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I (chartAt H x x) (chartAt H x).symm y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
theorem writtenInExtChartAt_extChartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I 𝓘(𝕜, E) x (extChartAt I x) y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
theorem writtenInExtChartAt_extChartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt 𝓘(𝕜, E) I (extChartAt I x x) (extChartAt I x).symm y = y := by
  simp_all only [mfld_simps]

theorem writtenInExtChartAt_mapsTo {x : M} {f : M → M'} :
    MapsTo (writtenInExtChartAt I I' x f)
      ((extChartAt I x).target ∩ f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source)
      (extChartAt I' (f x)).target := by
  intro x' hx'
  simpa using (chartAt H' (f x)).mapsTo (by simpa using hx'.2)

section

variable {G G' F F' N N' : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace G] [TopologicalSpace N] [TopologicalSpace G'] [TopologicalSpace N']
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  [ChartedSpace G N] [ChartedSpace G' N']

set_option backward.isDefEq.respectTransparency false in
lemma writtenInExtChartAt_prod {f : M → N} {g : M' → N'} {x : M} {x' : M'} :
    (writtenInExtChartAt (I.prod I') (J.prod J') (x, x') (Prod.map f g)) =
      Prod.map (writtenInExtChartAt I J x f) (writtenInExtChartAt I' J' x' g) := by
  ext p <;>
  simp [writtenInExtChartAt, I.toPartialEquiv.prod_symm, (chartAt H x).toPartialEquiv.prod_symm]

@[deprecated (since := "2026-02-18")] alias writtenInExtChart_prod := writtenInExtChartAt_prod

end

variable (𝕜)

theorem extChartAt_self_eq {x : H} : ⇑(extChartAt I x) = I :=
  rfl

theorem extChartAt_self_apply {x y : H} : extChartAt I x y = I y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity. -/
theorem extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E := by
  simp only [mfld_simps]

theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl

variable {𝕜}

set_option backward.isDefEq.respectTransparency false in
theorem extChartAt_prod (x : M × M') :
    extChartAt (I.prod I') x = (extChartAt I x.1).prod (extChartAt I' x.2) := by
  simp only [mfld_simps]
  rw [PartialEquiv.prod_trans]

theorem extChartAt_comp [ChartedSpace H H'] (x : M') :
    (letI := ChartedSpace.comp H H' M'; extChartAt I x) =
      (chartAt H' x).toPartialEquiv ≫ extChartAt I (chartAt H' x x) :=
  PartialEquiv.trans_assoc ..

theorem writtenInExtChartAt_chartAt_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'; writtenInExtChartAt I I x (chartAt H' x) y) = y := by
  letI := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

theorem writtenInExtChartAt_chartAt_symm_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'
     writtenInExtChartAt I I (chartAt H' x x) (chartAt H' x).symm y) = y := by
  letI := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

end ExtendedCharts

section Topology

-- Let `M` be a topological manifold over the field 𝕜.
variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A finite-dimensional manifold modelled on a locally compact field
(such as ℝ, ℂ or the `p`-adic numbers) is locally compact. -/
lemma Manifold.locallyCompact_of_finiteDimensional
    (I : ModelWithCorners 𝕜 E H) [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] :
    LocallyCompactSpace M := by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

variable (M)

/-- A locally compact manifold must be modelled on a locally compact space. -/
lemma LocallyCompactSpace.of_locallyCompact_manifold (I : ModelWithCorners 𝕜 E H)
    [h : Nonempty M] [LocallyCompactSpace M] :
    LocallyCompactSpace E := by
  rcases h with ⟨x⟩
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I x
  have h'y : y ∈ (extChartAt I x).target := interior_subset hy
  obtain ⟨s, hmem, hss, hcom⟩ :=
    LocallyCompactSpace.local_compact_nhds ((extChartAt I x).symm y) (extChartAt I x).source
      ((isOpen_extChartAt_source x).mem_nhds ((extChartAt I x).map_target h'y))
  have : IsCompact <| (extChartAt I x) '' s :=
    hcom.image_of_continuousOn <| (continuousOn_extChartAt x).mono hss
  apply this.locallyCompactSpace_of_mem_nhds_of_addGroup (x := y)
  rw [← (extChartAt I x).right_inv h'y]
  apply extChartAt_image_nhds_mem_nhds_of_mem_interior_range
    (PartialEquiv.map_target (extChartAt I x) h'y) _ hmem
  simp only [(extChartAt I x).right_inv h'y]
  exact interior_mono (extChartAt_target_subset_range x) hy

/-- Riesz's theorem applied to manifolds: a locally compact manifold must be modelled on a
finite-dimensional space. This is the converse to `Manifold.locallyCompact_of_finiteDimensional`. -/
theorem FiniteDimensional.of_locallyCompact_manifold
    [CompleteSpace 𝕜] (I : ModelWithCorners 𝕜 E H) [Nonempty M] [LocallyCompactSpace M] :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_locallyCompact_manifold M I
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

end Topology
