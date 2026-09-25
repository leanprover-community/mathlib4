/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Interior and boundary of a manifold
Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `x ∈ M` is an interior point if, with `φ` being the preferred chart at `x`,
  `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `x ∈ M` is a boundary point if `(extChartAt I x) x ∈ frontier (range I)`.
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `ModelWithCorners.univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `ModelWithCorners.interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- `BoundarylessManifold.isInteriorPoint`: if `M` is boundaryless, every point is an interior point
- `ModelWithCorners.Boundaryless.boundary_eq_empty` and `of_boundary_eq_empty`:
  `M` is boundaryless if and only if its boundary is empty

- `isInteriorPoint_iff_of_mem_atlas`: a point is an interior point iff any given chart around it
  sends it to the interior of the model; that is, the notion of interior is independent of choices
  of charts
- `ModelWithCorners.isOpen_interior`, `ModelWithCorners.isClosed_boundary`: the interior is open and
  and the boundary is closed. This is currently only proven for C¹ manifolds.

- `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`: differentiable maps with surjective
  differential send interior points to interior points
- `IsLocalDiffeomorphAt.isInteriorPoint_iff` etc.: local diffeomorphisms preserve both the boundary
  and interior

- `ModelWithCorners.interior_open`: the interior of `u : Opens M` is the preimage of the interior
  of `M` under the inclusion
- `ModelWithCorners.boundary_open`: the boundary of `u : Opens M` is the preimage of the boundary
  of `M` under the inclusion
- `ModelWithCorners.BoundarylessManifold.open`: if `M` is boundaryless, so is `u : Opens M`

- `ModelWithCorners.interior_prod`: the interior of `M × N` is the product of the interiors
  of `M` and `N`.
- `ModelWithCorners.boundary_prod`: the boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
- `ModelWithCorners.BoundarylessManifold.prod`: if `M` and `N` are boundaryless, so is `M × N`

- `ModelWithCorners.interior_disjointUnion`: the interior of a disjoint union `M ⊔ M'`
  is the union of the interior of `M` and `M'`
- `ModelWithCorners.boundary_disjointUnion`: the boundary of a disjoint union `M ⊔ M'`
  is the union of the boundaries of `M` and `M'`
- `ModelWithCorners.boundaryless_disjointUnion`: if `M` and `M'` are boundaryless,
  so is their disjoint union `M ⊔ M'`

## Tags
manifold, interior, boundary

## TODO
- the interior of `M` is dense, the boundary nowhere dense
- the interior of `M` is a boundaryless manifold
- `boundary M` is a submanifold (possibly with boundary and corners):
  follows from the corresponding statement for the model with corners `I`;
  this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero
- generalise lemmas about C¹ manifolds with boundary to also hold for finite-dimensional topological
  manifolds; this will require e.g. the homology of spheres.
- submersions send interior points to interior points. This should be an easy consequence of
  `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv` once submersions are defined.

-/

@[expose] public section

open Set Function
open scoped Topology Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in
/-- `p ∈ M` is an interior point of a manifold `M` if and only if its image in the extended chart
lies in the interior of the model space. -/
def IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

variable (I) in
/-- `p ∈ M` is a boundary point of a manifold `M` if and only if its image in the extended chart
lies on the boundary of the model space. -/
def IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

variable (M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x }

lemma isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target :=
  ⟨fun h ↦ (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h ↦ OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

variable (M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

lemma isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) :=
  Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  rw [IsInteriorPoint, or_iff_not_imp_left, I.isBoundaryPoint_iff, ← closure_diff_interior,
    I.isClosed_range.closure_eq, mem_diff]
  exact fun h ↦ ⟨mem_range_self _, h⟩

/-- A manifold decomposes into interior and boundary. -/
lemma interior_union_boundary_eq_univ : (I.interior M) ∪ (I.boundary M) = (univ : Set M) :=
  eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of a manifold `M` are disjoint. -/
lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact ⟨h1, h2⟩

lemma isInteriorPoint_iff_not_isBoundaryPoint (x : M) :
    I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x := by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact h

lemma isBoundaryPoint_iff_not_isInteriorPoint (x : M) :
    I.IsBoundaryPoint x ↔ ¬I.IsInteriorPoint x := by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

/-- The boundary is the complement of the interior. -/
lemma compl_interior : (I.interior M)ᶜ = I.boundary M := by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

/-- The interior is the complement of the boundary. -/
lemma compl_boundary : (I.boundary M)ᶜ = I.interior M := by
  rw [← compl_interior, compl_compl]

lemma _root_.range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I ∈ 𝓝 (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

/-- Type class for manifold without boundary. This differs from `ModelWithCorners.Boundaryless`,
which states that the `ModelWithCorners` maps to the whole model vector space. -/
class _root_.BoundarylessManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  isInteriorPoint' : ∀ x : M, IsInteriorPoint I x

section Boundaryless
variable [I.Boundaryless]

/-- Boundaryless `ModelWithCorners` implies boundaryless manifold. -/
instance : BoundarylessManifold I M where
  isInteriorPoint' x := by
    let r := ((chartAt H x).isOpen_extend_target (I := I)).interior_eq
    have : extChartAt I x = (chartAt H x).extend I := rfl
    rw [← this] at r
    rw [isInteriorPoint_iff, r]
    exact PartialEquiv.map_source _ (mem_extChartAt_source _)

end Boundaryless

section BoundarylessManifold

/-- The empty manifold is boundaryless. -/
instance BoundarylessManifold.of_empty [IsEmpty M] : BoundarylessManifold I M where
  isInteriorPoint' x := (IsEmpty.false x).elim

lemma _root_.BoundarylessManifold.isInteriorPoint {x : M} [BoundarylessManifold I M] :
    IsInteriorPoint I x := BoundarylessManifold.isInteriorPoint' x

/-- If `I` is boundaryless, `M` has full interior. -/
lemma interior_eq_univ [BoundarylessManifold I M] : I.interior M = univ :=
  eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

/-- Boundaryless manifolds have empty boundary. -/
lemma Boundaryless.boundary_eq_empty [BoundarylessManifold I M] : I.boundary M = ∅ := by
  rw [← I.compl_interior, I.interior_eq_univ, compl_empty_iff]

instance [BoundarylessManifold I M] : IsEmpty (I.boundary M) :=
  isEmpty_coe_sort.mpr Boundaryless.boundary_eq_empty

/-- `M` is boundaryless if and only if its boundary is empty. -/
lemma Boundaryless.iff_boundary_eq_empty : I.boundary M = ∅ ↔ BoundarylessManifold I M := by
  refine ⟨fun h ↦ { isInteriorPoint' := ?_ }, fun a ↦ boundary_eq_empty⟩
  intro x
  change x ∈ I.interior M
  rw [← compl_interior, compl_empty_iff] at h
  rw [h]
  trivial

/-- Manifolds with empty boundary are boundaryless. -/
lemma Boundaryless.of_boundary_eq_empty (h : I.boundary M = ∅) : BoundarylessManifold I M :=
  (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

end BoundarylessManifold

section ChartIndependence

/-- If a function `f : E → H` is differentiable at `x`, sends a neighbourhood `u` of `x` to a
closed convex set `s` with nonempty interior and has surjective differential at `x`, it must send
`x` to the interior of `s`. -/
lemma _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → H} {x : E} (hf : DifferentiableAt ℝ f x) {u : Set E} (hu : u ∈ 𝓝 x) {s : Set H}
    (hs : Convex ℝ s) (hs' : IsClosed s) (hs'' : (interior s).Nonempty) (hfus : Set.MapsTo f u s)
    (hfx : Function.Surjective (fderiv ℝ f x)) : f x ∈ interior s := by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : ∀ y, F (fderiv ℝ f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; push_neg
    refine ⟨f x - y, fun z ↦ ne_of_apply_ne F ?_⟩
    rw [h z, F.map_sub]
    exact (sub_pos.2 <| hF _ hy).ne
  -- This follows from `F ∘ f` taking on a local maximum at `e.extend I x`.
  have hF' : MapsTo F s (Iic (F (f x))) := by
    rw [← hs'.closure_eq, ← closure_Iio, ← hs.closure_interior_eq_closure_of_nonempty_interior hs'']
    exact .closure hF F.continuous
  have hFφ : IsLocalMax (F ∘ f) x := Filter.eventually_of_mem hu fun y hy ↦ hF' <| hfus hy
  have h := hFφ.fderiv_eq_zero
  rw [fderiv_comp _ (by fun_prop) hf, ContinuousLinearMap.fderiv] at h
  exact DFunLike.congr_fun h

variable {n : WithTop ℕ∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H} {x : M}

/-- For any two charts `e`, `e'` around a point `x` in a C¹ manifold, if `e` maps `x` to the
interior of the model space, `e'` does too - in other words, the notion of interior points does not
depend on any choice of charts.

Note that in general, this is actually quite nontrivial; that is why are focusing only on C¹
manifolds here. For merely topological finite-dimensional manifolds the proof involves singular
homology, and for infinite-dimensional topological manifolds I don't even know if this lemma holds.
-/
lemma mem_interior_range_of_mem_interior_range_of_mem_atlas (hn : n ≠ 0)
    (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  /- Since transition maps are diffeomorphisms, it suffices to show that if `e'` were to send `x`
  to the boundary of `range I`, the differential of the transition map `φ` from `e` to `e'` at `x`
  could not be surjective. -/
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he') <| by simp [hex, hex']).surjective
  intro hφx'
  /- Reduce the situation to the real case, then apply
  `DifferentiableAt.mem_interior_convex_of_surjective_fderiv`. -/
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- For any two charts `e`, `e'` around a point `x` in a C¹ manifold, `e` maps `x` to the interior
of the model space iff `e'` does. - in other words, the notion of interior points does not
depend on any choice of charts. -/
lemma mem_interior_range_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
    e'.extend I x ∈ interior (e'.extend I).target := by
  constructor <;> apply mem_interior_range_of_mem_interior_range_of_mem_atlas hn <;> assumption

/-- A point `x` in a C¹ manifold is an interior point if and only if it gets mapped to the interior
of the model space by any given chart - in other words, the notion of interior points does not
depend on any choice of charts. -/
lemma isInteriorPoint_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_atlas hn (chart_mem_atlas H x) he (mem_chart_source H x) hx

/-- A point `x` in a C¹ manifold is a boundary point if and only if it gets mapped to the boundary
of the model space by any given chart - in other words, the notion of boundary points does not
depend on any choice of charts.

Also see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
lemma isBoundaryPoint_iff_of_mem_atlas (hn : n ≠ 0) (he : e ∈ atlas H M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (e.extend I).target := by
  rw [← not_iff_not, ← I.isInteriorPoint_iff_not_isBoundaryPoint,
    I.isInteriorPoint_iff_of_mem_atlas hn he hx, mem_interior_iff_notMem_frontier]
  exact (e.extend I).mapsTo <| e.extend_source (I := I) ▸ hx

/-- The interior of any C¹ manifold is open.

This is currently only proven for C¹ manifolds, but holds at least for finite-dimensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
protected lemma isOpen_interior (hn : n ≠ 0) : IsOpen (I.interior M) := by
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ⟨_, ?_, isOpen_extChartAt_preimage (I := I) x
    isOpen_interior, mem_chart_source H x, isInteriorPoint_iff.1 hx⟩
  exact fun y hy ↦ (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).2 hy.2

/-- The boundary of any C¹ manifold is closed.

This is currently only proven for C¹ manifolds, but holds at least for finite-dimensional
topological manifolds too; see `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`. -/
protected lemma isClosed_boundary (hn : n ≠ 0) : IsClosed (I.boundary M) := by
  rw [← I.compl_interior, isClosed_compl_iff]
  exact I.isOpen_interior hn

end ChartIndependence

end ModelWithCorners

/-! Interior and boundary are preserved under (local) diffeomorphisms. -/
section Diffeomorph

open ModelWithCorners

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- If a function `f` is differentiable at `x` with surjective `mfderiv I I' f x` and `x` is an
interior point with respect to `I`, `f x` must be an interior point with respect to `I'`. -/
lemma MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv {f : M → N} {x : M}
    (hf : MDifferentiableAt I I' f x) (hf' : Surjective (mfderiv I I' f x))
    (hx : I.IsInteriorPoint x) : I'.IsInteriorPoint (f x) := by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : NormedSpace ℝ E' := NormedSpace.restrictScalars ℝ 𝕜 E'
  -- Write everything in terms of extended charts around `x` and `f x`.
  simp only [mfderiv, hf, ite_true] at hf'
  have hf'' := hf.differentiableWithinAt_writtenInExtChartAt.differentiableAt <| by
    simpa [← mem_interior_iff_mem_nhds] using hx
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ <| by simp) hf''] at hf'
  /- Since `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x`
  over `𝕜`, it also is so over `ℝ`. -/
  replace hf' : Surjective (fderiv ℝ (writtenInExtChartAt I I' x f) (extChartAt I x x)) := by
    rwa [hf''.fderiv_restrictScalars (𝕜 := ℝ), ContinuousLinearMap.coe_restrictScalars']
  replace hf'' := hf''.restrictScalars ℝ
  /- The lemma is now essentially just `mem_interior_convex_of_surjective_fderiv`: because
  `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x` over `ℝ` and
  sends a neighbourhood of `x` (the region in which it could be written in the extended charts) to
  a closed convex set with nonempty interior (`I'.range`), it must send `x` to that interior. -/
  have := hf''.mem_interior_convex_of_surjective_fderiv (Filter.inter_mem ?_ ?_) I'.convex_range
    I'.isClosed_range I'.nonempty_interior (writtenInExtChartAt_mapsTo.mono_right ?_) hf'
  · simpa using this
  · rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hx)]
    exact extChartAt_target_mem_nhdsWithin x
  · exact extChartAt_preimage_mem_nhds <| hf.continuousAt.preimage_mem_nhds <|
      extChartAt_source_mem_nhds _
  · exact extChartAt_target_subset_range _

lemma IsLocalDiffeomorphAt.isInteriorPoint_iff (hn : n ≠ 0) {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsInteriorPoint x ↔ I'.IsInteriorPoint (f x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (hf.mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).surjective
  · rw [← hf.localInverse_left_inv hf.localInverse_mem_target]
    refine (hf.localInverse_mdifferentiableAt hn).isInteriorPoint_of_surjective_mfderiv ?_ h
    exact (hf.mfderivToContinuousLinearEquiv hn).symm.surjective

lemma IsLocalDiffeomorphAt.isBoundaryPoint_iff (hn : n ≠ 0) {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I I' n f x) : I.IsBoundaryPoint x ↔ I'.IsBoundaryPoint (f x) := by
  simp [isBoundaryPoint_iff_not_isInteriorPoint, hf.isInteriorPoint_iff hn]


lemma IsLocalDiffeomorphOn.preimage_interior_inter (hn : n ≠ 0) {f : M → N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.interior N ∩ s = I.interior M ∩ s := by
  ext x
  simpa using fun hx ↦ ((hf ⟨x, hx⟩).isInteriorPoint_iff hn).symm

lemma IsLocalDiffeomorphOn.preimage_boundary_inter (hn : n ≠ 0) {f : M → N} {s : Set M}
    (hf : IsLocalDiffeomorphOn I I' n f s) : f ⁻¹' I'.boundary N ∩ s = I.boundary M ∩ s := by
  ext x
  simpa using fun hx ↦ ((hf ⟨x, hx⟩).isBoundaryPoint_iff hn).symm

lemma IsLocalDiffeomorph.preimage_interior (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.interior N = I.interior M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_interior_inter hn

lemma IsLocalDiffeomorph.preimage_boundary (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) : f ⁻¹' I'.boundary N = I.boundary M := by
  simpa using (hf.isLocalDiffeomorphOn univ).preimage_boundary_inter hn

lemma IsLocalDiffeomorph.boundarylessManifold (hn : n ≠ 0) {f : M → N}
    (hf : IsLocalDiffeomorph I I' n f) [BoundarylessManifold I' N] : BoundarylessManifold I M := by
  simp [← Boundaryless.iff_boundary_eq_empty, ← hf.preimage_boundary hn,
    Boundaryless.boundary_eq_empty]

lemma Diffeomorph.preimage_interior (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.interior N = I.interior M :=
  Φ.isLocalDiffeomorph.preimage_interior hn

lemma Diffeomorph.preimage_boundary (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ ⁻¹' I'.boundary N = I.boundary M :=
  Φ.isLocalDiffeomorph.preimage_boundary hn

lemma Diffeomorph.image_interior (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.interior M = I'.interior N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_interior hn).symm

lemma Diffeomorph.image_boundary (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    Φ '' I.boundary M = I'.boundary N :=
  (Φ.eq_preimage_iff_image_eq _ _).1 (Φ.preimage_boundary hn).symm

lemma Diffeomorph.boundarylessManifold (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N)
    [BoundarylessManifold I M] : BoundarylessManifold I' N :=
    Φ.symm.isLocalDiffeomorph.boundarylessManifold hn

lemma Diffeomorph.boundarylessManifold_iff (hn : n ≠ 0) (Φ : M ≃ₘ^n⟮I, I'⟯ N) :
    BoundarylessManifold I M ↔ BoundarylessManifold I' N :=
  ⟨fun _ ↦ Φ.boundarylessManifold hn, fun _ ↦ Φ.symm.boundarylessManifold hn⟩

end Diffeomorph

namespace ModelWithCorners

/-! Interior and boundary of open subsets of a manifold. -/
section opens

open TopologicalSpace

/-- For `u : Opens M`, `x : u` is an interior point iff `x.val : M` is. -/
lemma isInteriorPoint_iff_isInteriorPoint_val {u : Opens M} {x : u} :
    I.IsInteriorPoint x ↔ I.IsInteriorPoint x.1 := by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using
    fun _ _ ↦ (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

/-- For `u : Opens M`, `x : u` is a boundary point iff `x.val : M` is. -/
lemma isBoundaryPoint_iff_isBoundaryPoint_val {u : Opens M} {x : u} :
    I.IsBoundaryPoint x ↔ I.IsBoundaryPoint x.1 := by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

/-- The interior of `u : Opens M` is the preimage of the interior of `M` under the inclusion. -/
lemma interior_open {u : Opens M} : I.interior u = (↑) ⁻¹' I.interior M := by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

/-- The boundary of `u : Opens M` is the preimage of the boundary of `M` under the inclusion. -/
lemma boundary_open {u : Opens M} : I.boundary u = (↑) ⁻¹' I.boundary M := by
  simp [← I.compl_interior, I.interior_open]

/-- Open subsets of boundaryless manifolds are boundaryless. -/
instance BoundarylessManifold.open [BoundarylessManifold I M] (u : Opens M) :
    BoundarylessManifold I u :=
  ⟨fun _ ↦ I.isInteriorPoint_iff_isInteriorPoint_val.2 BoundarylessManifold.isInteriorPoint⟩

end opens

/-! Interior and boundary of the product of two manifolds. -/
section prod

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'} {x : M} {y : N}

set_option backward.isDefEq.respectTransparency false in
/-- The interior of `M × N` is the product of the interiors of `M` and `N`. -/
lemma interior_prod :
    (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interior N) := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq, ← range_prodMap, modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint, ← aux] at hp
    exact hp
  · change (I.prod J).IsInteriorPoint p
    rw [IsInteriorPoint, ← aux, mem_prod]
    obtain h := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h
    exact h

/-- The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`. -/
lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) ∪ Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.compl_interior, J.compl_interior, union_comm]
  rfl

/-- If `M` is boundaryless, `∂(M×N) = M × ∂N`. -/
lemma boundary_of_boundaryless_left [BoundarylessManifold I M] :
    (I.prod J).boundary (M × N) = Set.prod (univ : Set M) (J.boundary N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this, union_empty]

/-- If `N` is boundaryless, `∂(M×N) = ∂M × N`. -/
lemma boundary_of_boundaryless_right [BoundarylessManifold J N] :
    (I.prod J).boundary (M × N) = Set.prod (I.boundary M) (univ : Set N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this, empty_union]

/-- The product of two boundaryless manifolds is boundaryless. -/
instance BoundarylessManifold.prod [BoundarylessManifold I M] [BoundarylessManifold J N] :
    BoundarylessManifold (I.prod J) (M × N) := by
  apply Boundaryless.of_boundary_eq_empty
  simp only [boundary_prod, Boundaryless.boundary_eq_empty, union_empty_iff]
  -- These are simp lemmas, but `simp` does not apply them on its own:
  -- presumably because of the distinction between `Prod` and `ModelProd`
  exact ⟨Set.prod_empty, Set.empty_prod⟩

end prod

/-! Interior and boundary of the disjoint union of two manifolds. -/
section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}

open Topology

lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inl x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inl x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

lemma interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inr x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

lemma boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inr x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

-- Converse to the previous direction: if `x` were not an interior point,
-- it had to be a boundary point, hence `p` were a boundary point also, contradiction.
lemma isInteriorPoint_disjointUnion_left {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]

lemma isInteriorPoint_disjointUnion_right {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]

lemma interior_disjointUnion :
    ModelWithCorners.interior (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.interior (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]

lemma boundary_disjointUnion : ModelWithCorners.boundary (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.boundary (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.boundary (I := I) M') := by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]

/-- If `M` and `M'` are boundaryless, so is their disjoint union `M ⊔ M'`. -/
instance boundaryless_disjointUnion
    [hM : BoundarylessManifold I M] [hM' : BoundarylessManifold I M'] :
    BoundarylessManifold I (M ⊕ M') := by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM hM' ⊢
  simp [boundary_disjointUnion, hM, hM']

end disjointUnion

end ModelWithCorners
