/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Winston Yin
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
- **IsBoundaryPoint x**: `p ∈ M` is a boundary point if, for `φ` being the preferred chart at `x`,
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `interior_isOpen`: `interior I M` is open
- `boundary_isClosed`: `boundary I M` is closed

**TODO**
- under suitable assumptions, `boundary I M` has empty interior
(if `M` is finite-dimensional, `boundary I M` should have measure 0, which implies this)
- `interior I M` is a manifold without boundary
  (need to upgrade the model used; map the charts from an open ball to entire ℝ^n)
- the boundary is a submanifold of codimension 1, perhaps with boundary and corners
(this requires a definition of submanifolds)

## Tags
manifold, interior, boundary
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

/-- `p ∈ M` is a boundary point of a manifold `M` iff it is not an interior point.
This means that, for `φ` being the preferred chart at `x`, `φ x` is not an interior point of
`φ.target`. We do not say "boundary point" as `frontier φ.target` has two components, one on the
boundary of range I and another on the boundary of e.target (which we don't want). -/
def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∉ interior (extChartAt I x).target

namespace SmoothManifoldWithCorners
-- FIXME(MR): can I enable dot notation, like `M.interior I` or so?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x}

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x}
end SmoothManifoldWithCorners

namespace LocalHomeomorph -- move to SmoothManifoldsWithCorners!
variable {e e' : LocalHomeomorph M H}

-- more general lemma underlying foobar. xxx: find a better name!
lemma foobar_abstract {f : LocalHomeomorph H H} {y : H} (hy : y ∈ f.source)
    (h : I y ∈ interior (range I)) : I (f y) ∈ interior (range I) := by
  sorry

-- xxx: needs better name!
-- the interior of the target of an extended local homeo is contained in the interior of its
-- model's range
lemma extend_interior_target_subset : interior (e.extend I).target ⊆ interior (range I) := by
  rw [e.extend_target, interior_inter, (e.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right _ _

-- xxx: find a good name!!
lemma foobaz {y : H} (hy : y ∈ e.target) (hy' : I y ∈ interior (range ↑I)) :
    I y ∈ interior (e.extend I).target := by
  rw [e.extend_target, interior_inter, (e.open_target.preimage I.continuous_symm).interior_eq,
    mem_inter_iff, mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

/-- If `e` and `e'` are two charts, the transition map maps interior points to interior points. -/
-- as we only need continuity property, e or e' being in the atlas is not required
lemma foobar {x : M} (hx : x ∈ e.source ∩ e'.source) :
    (e.extend I) x ∈ interior (e.extend I).target ↔
    (e'.extend I) x ∈ interior (e'.extend I).target := by
  rcases ((mem_inter_iff x _ _).mp hx) with ⟨hxe, hxe'⟩
  -- reduction, step 1: simplify what the interior means
  have : (e.extend I) x ∈ interior (e.extend I).target ↔ I (e x) ∈ interior (range I) :=
    ⟨fun hx ↦ extend_interior_target_subset hx, fun hx ↦ foobaz (e.map_source hxe) hx⟩
  rw [this]
  have : (e'.extend I) x ∈ interior (e'.extend I).target ↔ I (e' x) ∈ interior (range I) :=
    ⟨fun hx ↦ extend_interior_target_subset hx, fun hx ↦ foobaz (e'.map_source hxe') hx⟩
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

namespace SmoothManifoldWithCorners
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
    I.IsBoundaryPoint x ↔ (e.extend I) x ∉ interior (e.extend I).target := by
  -- This lemma is just the "negation" (applying not_iff_not) to isInteriorPoint_iff.
  rw [← not_iff_not.mpr (isInteriorPoint_iff I hx)]
  exact Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases extChartAt I x x ∈ interior (extChartAt I x).target
  · exact Or.inl h
  · exact Or.inr h

variable (I M) in
/-- A manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) :=
  le_antisymm (fun _ _ ↦ trivial) (fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of `M` are disjoint. -/ -- xxx: name `..._eq_empty` instead?
lemma interior_boundary_disjoint :
    (SmoothManifoldWithCorners.interior I M) ∩ (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  ext
  exact ⟨fun h ↦ (not_mem_of_mem_diff h) (mem_of_mem_diff h), by exfalso⟩

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
  have : (SmoothManifoldWithCorners.interior I M)ᶜ = SmoothManifoldWithCorners.boundary I M :=
    (compl_unique interior_boundary_disjoint (univ_eq_interior_union_boundary I M))
  rw [← this, compl_compl]
  exact interior_isOpen
end SmoothManifoldWithCorners

-- TODO: interior I M is a manifold
