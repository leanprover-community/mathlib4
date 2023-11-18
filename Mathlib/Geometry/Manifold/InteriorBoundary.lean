/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Winston Yin
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

-- FIXME: should this be its own file or go in SmoothManifoldWithCorners?
-- the latter is already huge, or its own file - move other results about boundaryless here?

/-!
## Interior and boundary of a smooth manifold

Define the interior and boundary of a smooth manifold.

**Main definitions**
- **IsInteriorPoint x**: `p ∈ M` is an interior point if, for `φ` being the preferred chart at `x`,
 `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `p ∈ M` is a boundary point if, for `φ` being the preferred chart at `x`,
- **SmoothManifoldWithBoundary.interior I M** is the **interior** of `M`, the set of its interior points.
- **SmoothManifoldWithBoundary.boundary I M** is the **boundary** of `M`, the set of its boundary points.

**Main results**:
- `xxx`: M is the union of its interior and boundary
- `yyy`: interior I M is open

**TODO**: show that
- interior I M is a manifold without boundary
  (need to upgrade the above; map the charts from an open ball to entire ℝ^n)
- the boundary is a submanifold of codimension 1 (once mathlib has submanifolds)

## Tags
manifold, interior, boundary
-/

-- Let M be a smooth manifold with corners over the pair (I,E).
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- `p ∈ M` is an interior point of a smooth manifold `M` iff
for `φ` being the preferred chart at `x`, `φ x` is an interior point of `φ.target`. -/
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (extChartAt I x).target
-- Otherwise, it is a boundary point.

def ModelWithCorners.IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (extChartAt I x).target

namespace SmoothManifoldWithCorners
-- FIXME(MR): can I enable dot notation, like `M.interior I` or so?

variable (I M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x}

variable (I M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x}

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

-- underlying lemma: if e and e' are two charts,
-- the transition map maps interior points to interior points and boundary to boundary
lemma foobar {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) {x : M}
  (hx : x ∈ e.source ∩ e'.source) :
  (e.extend I) x ∈ interior (e.extend I).target ↔
    (e'.extend I) x ∈ interior (e'.extend I).target := sorry

lemma foobar' {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) {x : M}
  (hx : x ∈ e.source ∩ e'.source) :
  (e.extend I) x ∈ frontier (e.extend I).target ↔
    (e'.extend I) x ∈ frontier (e'.extend I).target := sorry

-- more abstract result: a local homeomorphism maps interior to interior and boundary to boundary

/-- Every point is either an interior or a boundary point. -/
lemma bar (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  set e := extChartAt I x
  set y := extChartAt I x x
  have : IsClosed I.target := I.target_eq ▸ (I.closed_range)
  -- TODO: this should be obvious now!
  have : IsClosed e.target := sorry
  have : y ∈ interior e.target ∪ frontier e.target := by
    rw [← closure_eq_interior_union_frontier (e.target), this.closure_eq]
    exact mem_extChartAt_target I x
  exact (Set.mem_union y _ _).mp this

-- Decomposition of M into interior and boundary. TODO: find nice name!
lemma foo : (SmoothManifoldWithCorners.interior I M) ∪ (SmoothManifoldWithCorners.boundary I M) = M := by
  -- FIXME: should follow from lemma `bar`
  sorry

/-- Ihe interior of a smooth manifold is an open subset. -/
lemma interior_isOpen : IsOpen (SmoothManifoldWithCorners.interior I M) := by
  -- use `isInteriorPoint_iff`
  sorry

-- interior I M is a smooth manifold (use TopologicalSpace.Opens.instSmoothManifoldWithCornersSubtypeMemOpensInstMembershipInstSetLikeOpensInstTopologicalSpaceSubtypeInstChartedSpace)
end SmoothManifoldWithCorners
