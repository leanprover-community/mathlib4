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
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners
/-- `p ∈ M` is an interior point of a manifold `M` iff its image in the extended chart
lies in the interior of the model space. -/
def IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

/-- `p ∈ M` is a boundary point of a manifold `M` iff its image in the extended chart
lies on the boundary of the model space. -/
def IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

variable (M) in
/-- The **interior** of a manifold `M` is the set of its interior points. -/
protected def interior : Set M := { x : M | I.IsInteriorPoint x }

lemma isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target :=
  ⟨fun h ↦ (chartAt H x).mem_interior_extend_target _ (mem_chart_target H x) h,
    fun h ↦ PartialHomeomorph.interior_extend_target_subset_interior_range _ _ h⟩

variable (M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

lemma isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) :=
  Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  by_cases h : extChartAt I x x ∈ interior (range I)
  · exact Or.inl h
  · right -- Otherwise, we have a boundary point.
    rw [I.isBoundaryPoint_iff, ← closure_diff_interior, I.closed_range.closure_eq]
    exact ⟨mem_range_self _, h⟩

/-- A manifold decomposes into interior and boundary. -/
lemma interior_union_boundary_eq_univ : (I.interior M) ∪ (I.boundary M) = (univ : Set M) :=
  le_antisymm (fun _ _ ↦ trivial) (fun x _ ↦ I.isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of a manifold `M` are disjoint. -/
lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  choose x hx using not_disjoint_iff.mp h
  rcases hx with ⟨h1, h2⟩
  show (extChartAt I x) x ∈ (∅ : Set E)
  rw [← disjoint_iff_inter_eq_empty.mp (disjoint_interior_frontier (s := range I))]
  exact ⟨h1, h2⟩

/-- The boundary is the complement of the interior. -/
lemma boundary_eq_complement_interior : I.boundary M = (I.interior M)ᶜ := by
  apply (compl_unique ?_ I.interior_union_boundary_eq_univ).symm
  exact disjoint_iff_inter_eq_empty.mp (I.disjoint_interior_boundary)

lemma _root_.range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I ∈ nhds (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

variable (M) in
/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class _root_.Boundaryless : Prop where
  isInteriorPoint : ∀ x : M, IsInteriorPoint I x
-- #align model_with_corners.boundaryless ModelWithCorners.Boundaryless

theorem Boundaryless.isInteriorPoint [_root_.Boundaryless I M] {x : M} :
    IsInteriorPoint I x := _root_.Boundaryless.isInteriorPoint x

/-- If `I` is a `ModelWithCorners.Boundaryless` model, then it is a homeomorphism. -/
@[simps (config := {simpRhs := true})]
def toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where
  __ := I
  left_inv := I.left_inv
  right_inv _ := I.right_inv <| I.range_eq_univ.symm ▸ mem_univ _

/-- The trivial model with corners has no boundary -/
instance _root_.modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩
#align model_with_corners_self_boundaryless modelWithCornersSelf_boundaryless

/-- If two model with corners are boundaryless, their product also is -/
instance range_eq_univ_prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.prod I').Boundaryless := by
  constructor
  dsimp [ModelWithCorners.prod, ModelProd]
  rw [← prod_range_range_eq, ModelWithCorners.Boundaryless.range_eq_univ,
    ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ]
#align model_with_corners.range_eq_univ_prod ModelWithCorners.range_eq_univ_prod

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem _root_.mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

lemma _root_.PartialHomeomorph.isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target := by
  rw [extend_target, I.range_eq_univ, inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target

section Boundaryless
variable [I.Boundaryless]

/-- If `I` is boundaryless, every point of `M` is an interior point. -/
lemma isInteriorPoint {x : M} : I.IsInteriorPoint x := by
  let r := ((chartAt H x).isOpen_extend_target I).interior_eq
  have : extChartAt I x = (chartAt H x).extend I := rfl
  rw [← this] at r
  rw [ModelWithCorners.isInteriorPoint_iff, r]
  exact PartialEquiv.map_source _ (mem_extChartAt_source _ _)

/-- If `I` is boundaryless, `M` has full interior. -/
lemma interior_eq_univ : I.interior M = univ := by
  ext
  refine ⟨fun _ ↦ trivial, fun _ ↦ I.isInteriorPoint⟩

/-- If `I` is boundaryless, `M` has empty boundary. -/
lemma Boundaryless.boundary_eq_empty : I.boundary M = ∅ := by
  rw [I.boundary_eq_complement_interior, I.interior_eq_univ, compl_empty_iff]

end Boundaryless
end ModelWithCorners
