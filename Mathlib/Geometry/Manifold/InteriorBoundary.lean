/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

-- FIXME: should this be its own file or go in SmoothManifoldWithCorners?
-- the latter is already huge, or its own file - move other results about boundaryless here?
-- xxx: if I can use dot notation, how set things up so they're also available for smooth manifolds?
-- manually re-declare them?

/-!
# Interior and boundary of a manifold
Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `p ∈ M` is an interior point if, for `φ` being the preferred chart at `x`,
 `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `p ∈ M` is a boundary point if, `(extChartAt I x) x ∈ frontier (range I)`.
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `interior_isOpen`: `interior I M` is open
- `boundary_isClosed`: `boundary I M` is closed
- `interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- if `M` is boundaryless, every point is an interior point

## Tags
manifold, interior, boundary

## TODO
- the interior of `M` is a smooth manifold without boundary
- `boundary M` is a smooth submanifold (possibly with boundary and corners):
- follows from the corresponding statement for the model with corners `I`;
- this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero
-/

open Set

-- Let `M` be a manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (contDiffGroupoid 0 I)]

/-- `p ∈ M` is an interior point of a manifold `M` iff
for `φ` being the preferred chart at `x`, `φ x` is an interior point of `φ.target`. -/
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (extChartAt I x).target

/-- `p ∈ M` is a boundary point of a manifold `M` iff its image in the extended chart
lies on the boundary of the model space. -/
def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

namespace SmoothManifoldWithCorners
-- TODO: can I enable dot notation as in, say, `M.interior I`?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x}

lemma _root_.ModelWithCorners.isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target := Iff.rfl

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x}

lemma _root_.ModelWithCorners.isBoundaryPoint_iff {x : M} :
    I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) := Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases h : extChartAt I x x ∈ interior (extChartAt I x).target
  · exact Or.inl h
  · right -- Otherwise, we have a boundary point.
    rw [I.isBoundaryPoint_iff, ← closure_diff_interior, I.closed_range.closure_eq]
    refine ⟨mem_range_self _, ?_⟩
    by_contra h'
    exact h ((chartAt H x).mem_interior_extend_target I (mem_chart_target H x) h')

/-- A manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) :=
  le_antisymm (fun _ _ ↦ trivial) (fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of a manifold `M` are disjoint. -/
lemma interior_boundary_disjoint :
    (SmoothManifoldWithCorners.interior I M) ∩ (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  choose x hx using nmem_singleton_empty.mp h
  rcases hx with ⟨h1, h2⟩
  show (extChartAt I x) x ∈ (∅ : Set E)
  rw [← interior_frontier_disjoint]
  exact ⟨(chartAt H x).interior_extend_target_subset_interior_range I h1, h2⟩

/-- The boundary is the complement of the interior. -/
lemma boundary_eq_complement_interior :
    SmoothManifoldWithCorners.boundary I M = (SmoothManifoldWithCorners.interior I M)ᶜ :=
  (compl_unique interior_boundary_disjoint univ_eq_interior_union_boundary).symm
end SmoothManifoldWithCorners

/-- If `M` has no boundary, every point of `M` is an interior point. -/
lemma ModelWithCorners.isInteriorPoint [I.Boundaryless] {x : M} : I.IsInteriorPoint x := by
  let r := ((chartAt H x).isOpen_extend_target I).interior_eq
  have : extChartAt I x = (chartAt H x).extend I := rfl
  rw [← this] at r
  rw [ModelWithCorners.IsInteriorPoint, r]
  exact LocalEquiv.map_source _ (mem_extChartAt_source _ _)

/-- If `I` is boundaryless, `M` has full interior interior. -/
lemma ModelWithCorners.interior_eq_univ [I.Boundaryless] :
    SmoothManifoldWithCorners.interior I M = univ := by
  ext
  refine ⟨fun _ ↦ trivial, fun _ ↦ I.isInteriorPoint⟩

/-- If `I` is boundaryless, `M` has empty boundary. -/
lemma ModelWithCorners.Boundaryless.boundary_eq_empty [I.Boundaryless] :
    SmoothManifoldWithCorners.boundary I M = ∅ := by
  rw [SmoothManifoldWithCorners.boundary_eq_complement_interior, I.interior_eq_univ,
    compl_empty_iff]

section OpenInterior
namespace LocalHomeomorph -- move to SmoothManifoldsWithCorners!
variable {e e' : LocalHomeomorph M H}

-- more general lemma underlying foobar. xxx: find a better name!
-- TODO: This requires e.g. the homology of spheres, hence is blocked on that arriving to mathlib.
lemma foobar_abstract {f : LocalHomeomorph H H} {y : H} (hy : y ∈ f.source)
    (h : I y ∈ interior (range I)) : I (f y) ∈ interior (range I) := by
  sorry

/-- If `e` and `e'` are two charts, the transition map maps interior points to interior points. -/
-- as we only need continuity property, e or e' being in the atlas is not required
lemma foobar {x : M} (hx : x ∈ e.source ∩ e'.source) :
    (e.extend I) x ∈ interior (e.extend I).target ↔
    (e'.extend I) x ∈ interior (e'.extend I).target := by
  rcases ((mem_inter_iff x _ _).mp hx) with ⟨hxe, hxe'⟩
  -- reduction, step 1: simplify what the interior means
  have : (e.extend I) x ∈ interior (e.extend I).target ↔ I (e x) ∈ interior (range I) :=
    ⟨fun hx ↦ interior_extend_target_subset_interior_range e _ hx,
     fun hx ↦ mem_interior_extend_target _ _ (e.map_source hxe) hx⟩
  rw [this]
  have : (e'.extend I) x ∈ interior (e'.extend I).target ↔ I (e' x) ∈ interior (range I) :=
    ⟨fun hx ↦ interior_extend_target_subset_interior_range e' _ hx,
     fun hx ↦ mem_interior_extend_target _ _ (e'.map_source hxe') hx⟩
  rw [this]
  -- step 2: rewrite in terms of coordinate changes
  constructor
  · intro h
    let f := e.symm.trans e'
    have h2 : e x ∈ f.source := by
      have : e.symm (e x) = x := e.left_inv' hxe
      rw [LocalHomeomorph.trans_source, mem_inter_iff (e x), e.symm_source, mem_preimage, this]
      exact ⟨e.map_source hxe, hxe'⟩
    rw [← (e.left_inv' hxe)]
    exact foobar_abstract h2 h
  · sorry -- exactly the same... what's the best way to deduplicate?
end LocalHomeomorph

-- FIXME(MR): find a better wording for the next two docstrings
variable (I) in
/-- Whether `x` is an interior point can equivalently be described by any chart
  whose source contains `x`. -/
-- as we only need continuity properties, `e` being in the atlas is not required
lemma isInteriorPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ (e.extend I) x ∈ interior (e.extend I).target :=
  (chartAt H x).foobar (mem_inter (mem_chart_source H x) hx)

variable (I) in
/-- Whether `x` is a boundary point of `M` can equivalently be described by any chart
whose source contains `x`. -/
lemma isBoundaryPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ (e.extend I) x ∈ frontier (range I) := by
  -- TODO: this is a non-trivial result, but will reduce to foobar. TODO!
  -- This lemma is just the "negation" (applying not_iff_not) to isInteriorPoint_iff.
  let r := not_iff_not.mpr (isInteriorPoint_iff I hx)
  sorry

/-- The interior of a manifold is an open subset. -/
lemma interior_isOpen : IsOpen (SmoothManifoldWithCorners.interior I M) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  -- Consider the preferred chart at `x`. Its extended chart has open interior.
  let e := chartAt H x
  let U := interior (e.extend I).target
  -- For all `y ∈ e.source`, `y` is an interior point iff its image lies in `U`.
  -- FIXME: should this be a separate lemma?
  refine ⟨(e.extend I).source ∩ (e.extend I) ⁻¹' U, ?_, ?_, ?_⟩
  · intro y hy
    rw [e.extend_source] at hy
    apply (isInteriorPoint_iff I (mem_of_mem_inter_left hy)).mpr
    exact mem_of_mem_inter_right (a := e.source) hy
  · exact (e.continuousOn_extend I).preimage_open_of_open (e.isOpen_extend_source I) isOpen_interior
  · have : x ∈ (e.extend I).source := by
      rw [e.extend_source]
      exact mem_chart_source H x
    exact mem_inter this hx

/-- The boundary of a manifold is a closed subset. -/
lemma boundary_isClosed : IsClosed (SmoothManifoldWithCorners.boundary I M) := by
  apply isOpen_compl_iff.mp
  rw [SmoothManifoldWithCorners.boundary_eq_complement_interior, compl_compl]
  exact interior_isOpen

-- TODO: interior I M is a manifold
-- TODO: boundaryless also

end OpenInterior
