/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Winston Yin
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

-- FIXME: should this be its own file or go in SmoothManifoldWithCorners?
-- the latter is already huge, or its own file - move other results about boundaryless here?

-- NB: all results in this file hold for topological manifolds

/-!
# Interior and boundary of a manifold

Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `p ∈ M` is an interior point if, for `φ` being the preferred chart at `x`,
 `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `p ∈ M` is a boundary point if, for `φ` being the preferred chart at `x`,
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `interior_isOpen`: `interior I M` is open
- `boundary_isClosed`: `boundary I M` is closed
- `interior_boundary_eq_empty`: `boundary I M` has empty interior
(this implies it has "measure zero", see different file)

**TODO**
- `interior I M` is a manifold without boundary
  (need to upgrade the model used; map the charts from an open ball to entire ℝ^n)
- the boundary is a submanifold of codimension 1 (once mathlib has submanifolds)

## Tags
manifold, interior, boundary
-/

open Set

-- Let `M` be a smooth manifold with corners over the pair `(E, H)`.
-- NB: smoothness is not required; all results in this file hold for topological manifolds.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- `p ∈ M` is an interior point of a smooth manifold `M` iff
for `φ` being the preferred chart at `x`, `φ x` is an interior point of `φ.target`. -/
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (extChartAt I x).target

/-- `p ∈ M` is a boundary point of a smooth manifold `M` iff it is not an interior point.
This means that, for `φ` being the preferred chart at `x`, `φ x` is not an interior point of
`φ.target`. We do not say "boundary point" as `frontier φ.target` has two components, one on the
boundary of range I and another on the boundary of e.target (which we don't want). -/
def ModelWithCorners.isBoundaryPoint (x : M) := extChartAt I x x ∉ interior (extChartAt I x).target

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
-- as we only need continuity properties, `e` being in the atlas is not required
lemma isInteriorPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.isInteriorPoint x ↔ (e.extend I) x ∈ interior (e.extend I).target := by
  sorry

/-- Whether `x` is a boundary point of `M` can equivalently be described by any chart
whose source contains `x`. -/
lemma isBoundaryPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.isBoundaryPoint x ↔ (e.extend I) x ∉ interior (e.extend I).target := by
  sorry

/-- Every point is either an interior or a boundary point. -/ -- FIXME: better name?!
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  set e := extChartAt I x
  set y := extChartAt I x x
  by_cases y ∈ interior e.target
  · have : I.isInteriorPoint x := (isInteriorPoint_iff (mem_chart_source H x) (I := I)).mpr h
    exact Or.inl h
  · have : I.isBoundaryPoint x := (isBoundaryPoint_iff (mem_chart_source H x) (I := I)).mpr h
    exact Or.inr h

/-- A manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) := by
  apply le_antisymm
  · exact fun x _ ↦ trivial
  · exact fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x

-- should be in mathlib; Mathlib.Topology.Basic
lemma interior_frontier_disjoint {X : Type*} [TopologicalSpace X] {s : Set X} :
    interior s ∩ frontier s = ∅ := by
  rw [← closure_diff_interior s]
  have : (closure s \ interior s) = closure s ∩ (interior s)ᶜ := rfl
  rw [this]
  rw [← inter_assoc, inter_comm, ← inter_assoc, compl_inter_self, empty_inter]

-- proper name? or _eq_emptyset?
/-- The interior and boundary of `M` are disjoint. -/
lemma interior_boundary_disjoint :
    (SmoothManifoldWithCorners.interior I M) ∩ (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  ext x
  constructor; intro h
  · exact (not_mem_of_mem_diff h) (mem_of_mem_diff h)
  · exfalso

/-- The interior of a manifold is an open subset. -/
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
    apply (isInteriorPoint_iff (mem_of_mem_inter_left hy)).mpr
    exact mem_of_mem_inter_right (a := e.source) hy
  · exact (e.continuousOn_extend I).preimage_open_of_open (e.isOpen_extend_source I) isOpen_interior
  · have : x ∈ (e.extend I).source := by
      rw [e.extend_source]
      exact mem_chart_source H x
    exact mem_inter this hx

/-- The boundary of a manifold is a closed subset. -/
lemma boundary_isClosed : IsClosed (SmoothManifoldWithCorners.boundary I M) := by
  apply isOpen_compl_iff.mp
  have : (SmoothManifoldWithCorners.interior I M)ᶜ = SmoothManifoldWithCorners.boundary I M :=
    (compl_unique interior_boundary_disjoint (univ_eq_interior_union_boundary (I := I) (M := M)))
  rw [← this, compl_compl]
  exact interior_isOpen

-- FIXME: good name? should go in Mathlib.Topology.Basic
lemma aux {X : Type*} [TopologicalSpace X] {s O t : Set X} (h : s = O ∩ t) (hO : IsOpen O) :
    s \ interior s ⊆ t \ interior t := by
  let aux := calc interior s
    _ = interior O ∩ interior t := by rw [h, interior_inter]
    _ = O ∩ interior t := by rw [hO.interior_eq]
  calc s \ interior s
    _ = (O ∩ t) \ (O ∩ interior t) := by rw [aux, h]
    _ = O ∩ (t \ interior t) := by rw [inter_diff_distrib_left]
    _ ⊆ t \ interior t := inter_subset_right _ _

-- is this a better lemma; is `aux` useful on its own?
lemma aux2 {X : Type*} [TopologicalSpace X] {s O t : Set X} (h : s = O ∩ t) (hO : IsOpen O)
    (ht : IsClosed t) : s \ interior s ⊆ frontier t :=
  ht.frontier_eq ▸ aux h hO

/-- The boundary of any extended chart has empty interior. -/
lemma __root__.LocalHomeomorph.extend_interior_boundary_eq_empty {e : LocalHomeomorph M H} :
    interior ((e.extend I).target \ interior (e.extend I).target) = ∅ := by
  -- `e.extend_target I = (I.symm ⁻¹' e.target) ∩ range I` is the union of an open set and a
  -- closed set: hence the frontier is contained in the second factor.
  have h1 : (e.extend I).target \ interior (e.extend I).target ⊆ frontier (range I) :=
    aux2 (e.extend_target I) (e.open_target.preimage I.continuous_symm) I.closed_range
  suffices interior (frontier (range I)) = ∅ by
    exact subset_eq_empty (interior_mono h1) this
  -- As `range I` is closed, its frontier has empty interior.
  exact interior_frontier I.closed_range

/-- The boundary of a manifold has empty interior. -/
lemma interior_boundary_eq_empty : interior (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  -- use `isBoundaryPoint_iff` and the previous lemma; similar to `interior_isOpen`
  sorry

-- interior I M is a manifold (use TopologicalSpace.Opens.instSmoothManifoldWithCornersSubtypeMemOpensInstMembershipInstSetLikeOpensInstTopologicalSpaceSubtypeInstChartedSpace)
end SmoothManifoldWithCorners
