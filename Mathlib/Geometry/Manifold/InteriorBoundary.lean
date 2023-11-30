/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

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
- `interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- if `M` is boundaryless, every point is an interior point

## Tags
manifold, interior, boundary

## TODO
- `x` is an interior point iff *any* chart around `x` maps it to `interior (range I)`;
similarly for the boundary.
- the interior of `M` is open, hence the boundary is closed (and nowhere dense)
  In finite dimensions, this requires e.g. the homology of spheres.
- the interior of `M` is a smooth manifold without boundary
- `boundary M` is a smooth submanifold (possibly with boundary and corners):
follows from the corresponding statement for the model with corners `I`;
this requires a definition of submanifolds
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
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

/-- `p ∈ M` is a boundary point of a manifold `M` iff its image in the extended chart
lies on the boundary of the model space. -/
def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

namespace SmoothManifoldWithCorners
-- TODO: can I enable dot notation as in, say, `M.interior I`?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x }

lemma _root_.ModelWithCorners.isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target :=
  ⟨fun h ↦ (chartAt H x).mem_interior_extend_target _ (mem_chart_target H x) h,
    fun h ↦ LocalHomeomorph.interior_extend_target_subset_interior_range _ _ h⟩

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

lemma _root_.ModelWithCorners.isBoundaryPoint_iff {x : M} :
    I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) := Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases h : extChartAt I x x ∈ interior (range I)
  · exact Or.inl h
  · right -- Otherwise, we have a boundary point.
    rw [I.isBoundaryPoint_iff, ← closure_diff_interior, I.closed_range.closure_eq]
    exact ⟨mem_range_self _, h⟩

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
  exact ⟨h1, h2⟩

/-- The boundary is the complement of the interior. -/
lemma boundary_eq_complement_interior :
    SmoothManifoldWithCorners.boundary I M = (SmoothManifoldWithCorners.interior I M)ᶜ :=
  (compl_unique interior_boundary_disjoint univ_eq_interior_union_boundary).symm
end SmoothManifoldWithCorners

lemma range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I ∈ nhds (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

section boundaryless
variable [I.Boundaryless]

/-- If `I` is boundaryless, every point of `M` is an interior point. -/
lemma ModelWithCorners.isInteriorPoint {x : M} : I.IsInteriorPoint x := by
  let r := ((chartAt H x).isOpen_extend_target I).interior_eq
  have : extChartAt I x = (chartAt H x).extend I := rfl
  rw [← this] at r
  rw [ModelWithCorners.isInteriorPoint_iff, r]
  exact LocalEquiv.map_source _ (mem_extChartAt_source _ _)

/-- If `I` is boundaryless, `M` has full interior. -/
lemma ModelWithCorners.interior_eq_univ : SmoothManifoldWithCorners.interior I M = univ := by
  ext
  refine ⟨fun _ ↦ trivial, fun _ ↦ I.isInteriorPoint⟩

/-- If `I` is boundaryless, `M` has empty boundary. -/
lemma ModelWithCorners.Boundaryless.boundary_eq_empty :
    SmoothManifoldWithCorners.boundary I M = ∅ := by
  rw [SmoothManifoldWithCorners.boundary_eq_complement_interior, I.interior_eq_univ,
    compl_empty_iff]

end boundaryless
