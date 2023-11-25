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
- if `M` is boundary, every point is an interior point

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

def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

namespace SmoothManifoldWithCorners
-- FIXME(MR): can I enable dot notation as in, say, `M.interior I`?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x}

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x}

lemma _root_.ModelWithCorners.isBoundaryPoint_iff {x : M} :
  I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) := Iff.rfl

-- move to LocalHomeomorph!
/-- The interior of `(e.extend I).target` is contained in the interior of its model's range. -/
lemma _root_.LocalHomeomorph.extend_interior_subset_interior_target22 {e : LocalHomeomorph M H} :
    interior (e.extend I).target ⊆ interior (range I) := by
  rw [e.extend_target, interior_inter, (e.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right _ _

/-- If `y ∈ e.target` and `I y ∈ interior (range I)`,, then `I y` is an interior point of `(I ∘ e).target`. -/
lemma _root_.LocalHomeomorph.mem_interior_extend_target {e : LocalHomeomorph M H} {y : H} (hy : y ∈ e.target)
    (hy' : I y ∈ interior (range I)) : I y ∈ interior (e.extend I).target := by
  rw [e.extend_target, interior_inter, (e.open_target.preimage I.continuous_symm).interior_eq,
    mem_inter_iff, mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases h : extChartAt I x x ∈ interior (extChartAt I x).target
  · exact Or.inl h
  · right -- Otherwise, we have a boundary point.
    rw [I.isBoundaryPoint_iff, ← closure_diff_interior, I.closed_range.closure_eq]
    refine ⟨mem_range_self _, ?_⟩
    by_contra h'
    exact h ((chartAt H x).mem_interior_extend_target (mem_chart_target H x) h')

variable (I M) in
/-- A manifold decomposes into interior and boundary. -/
lemma univ_eq_interior_union_boundary : (SmoothManifoldWithCorners.interior I M) ∪
    (SmoothManifoldWithCorners.boundary I M) = (univ : Set M) :=
  le_antisymm (fun _ _ ↦ trivial) (fun x _ ↦ isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of `M` are disjoint. -/
lemma interior_boundary_disjoint :
    (SmoothManifoldWithCorners.interior I M) ∩ (SmoothManifoldWithCorners.boundary I M) = ∅ := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  choose x hx using nmem_singleton_empty.mp h
  rcases hx with ⟨h1, h2⟩

  rw [SmoothManifoldWithCorners.boundary] at h2
  have : I.IsBoundaryPoint x := sorry
  rw [I.isBoundaryPoint_iff (x := x)] at this
  have aux2 : frontier (range I) ∩ interior (range I) = ∅ := sorry -- topology
  have : (extChartAt I x) x ∈ interior (range I) := by
    sorry --apply?--sorry
  have aux : (extChartAt I x) x ∈ (∅ : Set E) := by
    rw [← aux2]
    rw [inter_comm] --xxx
    exact ⟨this, h2⟩
  exact aux


  -- have prev : (extChartAt I x) x ∉ interior (range I) := by -- copied; deduplicate
  --   by_contra h2
  --   have : I ((chartAt H x) x) ∈ interior (extChartAt I x).target := by
  --     simp_rw [← Function.comp_apply]
  --     exact (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h2
  --   sorry--exact?-- h this
  -- have : (extChartAt I x) x ∉ interior ((chartAt H x).extend I).target := by
  --   by_contra h
  --   exact prev ((chartAt H x).extend_interior_subset_interior_target22 (I := I) h1)
  -- exact this h1
end SmoothManifoldWithCorners
