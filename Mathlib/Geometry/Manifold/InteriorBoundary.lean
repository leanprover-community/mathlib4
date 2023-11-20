/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Winston Yin
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

-- FIXME: should this be its own file or go in SmoothManifoldWithCorners?
-- the latter is already huge, or its own file - move other results about boundaryless here?

/-!
# Interior and boundary of a smooth manifold

Define the interior and boundary of a smooth manifold.

## Main definitions
- **IsInteriorPoint x**: `p ∈ M` is an interior point if, for `φ` being the preferred chart at `x`,
 `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `p ∈ M` is a boundary point if, for `φ` being the preferred chart at `x`,
- **SmoothManifoldWithBoundary.interior I M** is the **interior** of `M`, the set of its interior
points.
- **SmoothManifoldWithBoundary.boundary I M** is the **boundary** of `M`, the set of its boundary
points.

## Main results
- `xxx`: M is the union of its interior and boundary
- `yyy`: interior I M is open

**TODO**: show that
- interior I M is a manifold without boundary
  (need to upgrade the above; map the charts from an open ball to entire ℝ^n)
- the boundary is a submanifold of codimension 1 (once mathlib has submanifolds)

## Tags
manifold, interior, boundary
-/

open Set

-- Let `M` be a smooth manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- `p ∈ M` is an interior point of a smooth manifold `M` iff
for `φ` being the preferred chart at `x`, `φ x` is an interior point of `φ.target`. -/
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (extChartAt I x).target

/-- `p ∈ M` is a boundary point of a smooth manifold `M` iff
for `φ` being the preferred chart at `x`, `φ x` is a boundary point of `φ.target`. -/
def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (extChartAt I x).target

namespace SmoothManifoldWithCorners
-- FIXME(MR): can I enable dot notation, like `M.interior I` or so?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x}

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x}

/-- If `e` and `e'` are two charts, the transition map maps interior points to interior points. -/
lemma foobar {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) {x : M}
    (hx : x ∈ e.source ∩ e'.source) :
      (e.extend I) x ∈ interior (e.extend I).target ↔
      (e'.extend I) x ∈ interior (e'.extend I).target := sorry

/-- If `e` and `e'` are two charts, the transition map maps boundary points to boundary points. -/
lemma foobar' {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) {x : M}
    (hx : x ∈ e.source ∩ e'.source) :
    (e.extend I) x ∈ frontier (e.extend I).target ↔
    (e'.extend I) x ∈ frontier (e'.extend I).target := sorry

-- more abstract result: a local homeomorphism maps interior to interior and boundary to boundary

-- FIXME(MR): find a better wording for the next two docstrings
/-- Whether `x` is an interior point can equivalently be described by any chart
  whose source contains `x`. -/
lemma isInteriorPoint_iff {e : LocalHomeomorph M H} (he : e ∈ atlas H M) {x : M}
    (hx : x ∈ e.source) : I.IsInteriorPoint x ↔ (e.extend I) x ∈ interior (e.extend I).target := by
  sorry

/-- Whether `x` is a boundary point of `M` can equivalently be described by any chart
whose source contains `x`. -/
lemma isBoundaryPoint_iff {e : LocalHomeomorph M H} (he : e ∈ atlas H M) {x : M}
    (hx : x ∈ e.source) : I.IsBoundaryPoint x ↔ (e.extend I) x ∈ frontier (e.extend I).target := by
  sorry

/-- Every point is either an interior or a boundary point. -/ -- FIXME: better name?!
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  set e := extChartAt I x
  set y := extChartAt I x x
  have : IsClosed I.target := I.target_eq ▸ (I.closed_range)
  -- TODO: this should be obvious now!
  have : IsClosed e.target := sorry
  have : y ∈ interior e.target ∪ frontier e.target := by
    rw [← closure_eq_interior_union_frontier (e.target), this.closure_eq]
    exact mem_extChartAt_target I x
  exact (mem_union y _ _).mp this

/-- A smooth manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) := by
  apply le_antisymm
  · exact fun x _ ↦ trivial
  · exact fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x

/-- Ihe interior of a smooth manifold is an open subset. -/
lemma interior_isOpen : IsOpen (SmoothManifoldWithCorners.interior I M) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  -- Consider the preferred chart at `x`. Its extended chart has open interior.
  let e := chartAt H x
  let U := interior (e.extend I).target
  -- For all `y ∈ e.source`, `y` is an interior point iff its image lies in `U`.
  -- FIXME: should this be a separate lemma?
  use (e.extend I).source ∩ (e.extend I) ⁻¹' U
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [e.extend_source] at hy
    apply (isInteriorPoint_iff (chart_mem_atlas H x) (mem_of_mem_inter_left hy)).mpr
    exact mem_of_mem_inter_right (a := e.source) hy
  · exact (e.continuousOn_extend I).preimage_open_of_open (e.isOpen_extend_source I) isOpen_interior
  · have : x ∈ (e.extend I).source := by
      rw [e.extend_source]
      exact mem_chart_source H x
    exact mem_inter this hx

/-- The boundary of any extended chart has empty interior. -/
-- NB: this is *false* for any set instead of `(e.extend I).target`:
-- for instance, $ℚ ⊆ ℝ$ has frontier ℝ (ℚ is dense in ℝ and ℚ has empty interior).
-- xxx: do I need that e is in the atlas? I think not; not double-checked.
-- xxx: is this lemma true with mathlib's current definitions?
lemma __root__.LocalHomeomorph.extend_interior_boundary_eq_empty {e : LocalHomeomorph M H} :
    interior (frontier (e.extend I).target) = ∅ := sorry

/-- The boundary of a smooth manifold has empty interior. -/
lemma interior_boundary_eq_empty : interior (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  -- use `isBoundaryPoint_iff` and the previous lemma; similar to `interior_isOpen`
  sorry

-- interior I M is a smooth manifold (use TopologicalSpace.Opens.instSmoothManifoldWithCornersSubtypeMemOpensInstMembershipInstSetLikeOpensInstTopologicalSpaceSubtypeInstChartedSpace)
end SmoothManifoldWithCorners
