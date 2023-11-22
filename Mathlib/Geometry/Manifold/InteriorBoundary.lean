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

section TopologyHelpers -- should be in mathlib; Mathlib.Topology.Basic
variable {X : Type*} [TopologicalSpace X] {s : Set X}

-- I don't need this lemma; is is useful independently itself?
lemma interior_frontier_disjoint : interior s ∩ frontier s = ∅ := by
  rw [← closure_diff_interior s, diff_eq]
  rw [← inter_assoc, inter_comm, ← inter_assoc, compl_inter_self, empty_inter]

-- FIXME: what's a good name?
lemma aux {O t : Set X} (h : s = O ∩ t) (hO : IsOpen O) :
    s \ interior s ⊆ t \ interior t := by
  rw [h, interior_inter, hO.interior_eq, ← inter_diff_distrib_left]
  exact inter_subset_right O (t \ interior t)

-- is this a better lemma; is `aux` useful on its own?
lemma aux2 {O t : Set X} (h : s = O ∩ t) (hO : IsOpen O)
    (ht : IsClosed t) : s \ interior s ⊆ frontier t := by
  rw [ht.frontier_eq, h, interior_inter, hO.interior_eq, ← inter_diff_distrib_left]
  exact inter_subset_right _ _
  -- alternative proof, if `aux` is useful: ht.frontier_eq ▸ aux h hO

end TopologyHelpers

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

/-- If `e` and `e'` are two charts, the transition map maps interior points to interior points. -/
-- as we only need continuity property, e or e' being in the atlas is not required
lemma foobar {e e' : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source ∩ e'.source) :
    (e.extend I) x ∈ interior (e.extend I).target ↔
    (e'.extend I) x ∈ interior (e'.extend I).target := sorry
-- both directions should be the same, more general lemma

-- FIXME(MR): find a better wording for the next two docstrings
variable (I) in
/-- Whether `x` is an interior point can equivalently be described by any chart
  whose source contains `x`. -/
-- as we only need continuity properties, `e` being in the atlas is not required
lemma isInteriorPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ (e.extend I) x ∈ interior (e.extend I).target :=
  foobar (mem_inter (mem_chart_source H x) hx)

variable (I) in
/-- Whether `x` is a boundary point of `M` can equivalently be described by any chart
whose source contains `x`. -/
lemma isBoundaryPoint_iff {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ (e.extend I) x ∉ interior (e.extend I).target := by
  -- This lemma is just the "negation" (applying not_iff_not) to isInteriorPoint_iff.
  rw [← not_iff_not.mpr (isInteriorPoint_iff I hx)]
  exact Iff.rfl

/-- Every point is either an interior or a boundary point. -/ -- FIXME: better name?!
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases extChartAt I x x ∈ interior (extChartAt I x).target
  · exact Or.inl h
  · exact Or.inr h

variable (I M) in
/-- A manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) := by
  apply le_antisymm
  · exact fun x _ ↦ trivial
  · exact fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x

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
  use (e.extend I).source ∩ (e.extend I) ⁻¹' U
  refine ⟨?_, ?_, ?_⟩
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

variable (I) in
/-- The boundary of any extended chart has empty interior. -/
lemma LocalHomeomorph.extend_interior_boundary_eq_empty {e : LocalHomeomorph M H} :
    interior ((e.extend I).target \ interior (e.extend I).target) = ∅ := by
  -- `e.extend_target I = (I.symm ⁻¹' e.target) ∩ range I` is the union of an open set and a
  -- closed set: hence the frontier is contained in the second factor.
  have h1 : (e.extend I).target \ interior (e.extend I).target ⊆ frontier (range I) :=
    aux2 (e.extend_target I) (e.open_target.preimage I.continuous_symm) I.closed_range
  suffices interior (frontier (range I)) = ∅ by
    exact subset_eq_empty (interior_mono h1) this
  -- As `range I` is closed, its frontier has empty interior.
  exact interior_frontier I.closed_range


lemma auxaux {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {O : Set X} {t : Set Y} (hO : IsOpen O) (hf : ContinuousOn f O) :
    interior (O ∩ f ⁻¹' t) = O ∩ f ⁻¹' (interior t) := by
  -- well, ⊇ always holds!
  have : interior (O ∩ f ⁻¹' t) ⊇ O ∩ f ⁻¹' (interior t) := by
    rw [interior_inter, hO.interior_eq]
    exact hf.preimage_interior_subset_interior_preimage hO

  -- **IF** f were an open map, I'd be happy... that only holds without boundary, though...
  have pretend : IsOpenMap f := sorry
  let r := pretend.interior_preimage_subset_preimage_interior (s := t)
  have : interior (O ∩ f ⁻¹' t) ⊆ O ∩ f ⁻¹' (interior t) := by
    rw [interior_inter, hO.interior_eq]
    exact inter_subset_inter_right O r
  sorry -- sCIFI!

/-- The charts of a charted space cover its domain. -/
-- {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
lemma ChartedSpace.covering : ⋃ x : M, (chartAt H x).source = univ := by
  apply subset_antisymm <;> intro y _
  · trivial
  · rw [mem_iUnion]
    use y
    exact mem_chart_source H y

namespace SmoothManifoldWithCorners
-- can I avoid using this lemma?
lemma covering : ⋃ x : M, (extChartAt I x).source = univ := by
  simp_rw [extChartAt_source]
  exact ChartedSpace.covering

lemma isBoundaryPoint_iff' {x : M} :
  SmoothManifoldWithCorners.boundary I M ∩ (extChartAt I x).source =
    (extChartAt I x).source ∩ (extChartAt I x) ⁻¹'
      ((extChartAt I x).target \ interior (extChartAt I x).target) := by
  have r' : (chartAt H x).extend I = extChartAt I x := rfl
  rw [← r']
  ext y
  -- This can surely be golfed: first three lines on both cases are the same.
  -- First steps: reorder target conditions; then try and_congr or so...
  constructor
  · rintro ⟨hbd, hsource⟩
    apply mem_inter hsource ?_ -- discharge first condition, easy
    rw [(chartAt H x).extend_source] at hsource
    let s := (isBoundaryPoint_iff I hsource).mp hbd
    -- This part can surely also be golfed!
    set e := chartAt H x
    set e' := e.extend I -- readability
    rw [mem_preimage]
    apply (mem_diff (e' y)).mpr
    constructor
    · rw [r', extChartAt_target]
      apply mem_inter ?_ (mem_range_self _)
      show I (e y) ∈ I.symm ⁻¹' e.target
      rw [mem_preimage, I.left_inv]
      exact e.map_source hsource
    · exact s
  · rintro ⟨hsource, hbd⟩
    apply mem_inter ?_ hsource
    rw [(chartAt H x).extend_source] at hsource
    apply (isBoundaryPoint_iff I hsource).mpr (not_mem_of_mem_diff hbd)

variable (I) in
/-- The boundary of a manifold has empty interior. -/
lemma interior_boundary_eq_empty : interior (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  set bd := SmoothManifoldWithCorners.boundary I M
  -- Now, compute.
  have := calc interior (bd)
    _ = interior (bd) ∩ univ := by rw [inter_univ]
    _ = interior (bd) ∩ ⋃ (x : M), (extChartAt I x).source := by simp_rw [covering]
    _ = interior (bd) ∩ ⋃ (x : M), interior ((extChartAt I x).source) := by
      have : ∀ x : M, interior ((extChartAt I x).source) = (extChartAt I x).source := by
        intro x
        have : extChartAt I x = (chartAt H x).extend I := rfl
        rw [this]
        exact (chartAt H x).isOpen_extend_source I (M := M).interior_eq
      simp_rw [this]
    _ = ⋃ (x : M), interior bd ∩ interior ((extChartAt I x).source) := inter_iUnion _ _
    _ = ⋃ (x : M), interior (bd ∩ (extChartAt I x).source) := by simp_rw [interior_inter]
    _ = ⋃ (x : M), interior ((extChartAt I x).source ∩
        (extChartAt I x) ⁻¹' ((extChartAt I x).target \ interior (extChartAt I x).target)) := by
      simp_rw [isBoundaryPoint_iff']

    -- this step is SCIFI: very happy if true!! need a rigorous argument, though
    -- extChart is continuous on its source, so this might hold?
    -- lemma: f is continuous, then interior f⁻¹'B = f⁻¹ (interior B)
    -- next up: f continuous on A, then A ∩ interior f⁻¹'(B) = f⁻¹(interior B) assuming f⁻¹B ⊆ A somehow
    _ = ⋃ (x : M), (extChartAt I x).source ∩ ((extChartAt I x) ⁻¹' (interior ((extChartAt I x).target \ interior (extChartAt I x).target))) := by
      have goal : ∀ x : M,  interior ((extChartAt I x).source ∩ (extChartAt I x) ⁻¹' ((extChartAt I x).target \ interior (extChartAt I x).target)) = (extChartAt I x).source ∩ ((extChartAt I x) ⁻¹' (interior ((extChartAt I x).target \ interior (extChartAt I x).target))) := by
        intro x
        set e := extChartAt I x
        let r := (chartAt H x).continuousOn_extend I
        have : (chartAt H x).extend I = e := rfl
        rw [this] at r
        -- interior (e.source ∩ ↑e ⁻¹' (e.target \ interior e.target)) = e.source ∩ ↑e ⁻¹' interior (e.target \ interior e.target)
        have : IsOpen e.source := sorry -- easy
        -- abstracted this into a lemma. now, let's see if that is actually true!!!
        -- well, one direction holds - but it's the wrong one...
        apply auxaux (O := e.source) this r (t := e.target \ interior e.target)
      simp_rw [goal]
      --let r := (chartAt H x).continuousOn_extend I
      --sorry

    _ = ⋃ (x : M), ∅ := by
      have aux : ∀ x : M, (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (interior ((extChartAt I x).target \ interior (extChartAt I x).target)) = ∅ := by
        intro x
        set e := extChartAt I x
        have : interior ((e.target \ interior e.target)) = ∅ := by
          have : (chartAt H x).extend I = e := rfl
          apply this ▸ ((chartAt H x).extend_interior_boundary_eq_empty (I := I))
        rw [this, preimage_empty, inter_empty]
      simp_rw [aux]
    _ = ∅ := iUnion_empty
  exact this

-- interior I M is a manifold (use TopologicalSpace.Opens.instSmoothManifoldWithCornersSubtypeMemOpensInstMembershipInstSetLikeOpensInstTopologicalSpaceSubtypeInstChartedSpace)
end SmoothManifoldWithCorners
