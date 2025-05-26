/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

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
- `ModelWithCorners.univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `ModelWithCorners.interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- `BoundarylessManifold.isInteriorPoint`: if `M` is boundaryless, every point is an interior point
- `ModelWithCorners.Boundaryless.boundary_eq_empty` and `of_boundary_eq_empty`:
`M` is boundaryless if and only if its boundary is empty

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
- `x` is an interior point iff *any* chart around `x` maps it to `interior (range I)`;
similarly for the boundary.
- the interior of `M` is open, hence the boundary is closed (and nowhere dense)
  In finite dimensions, this requires e.g. the homology of spheres.
- the interior of `M` is a manifold without boundary
- `boundary M` is a submanifold (possibly with boundary and corners):
follows from the corresponding statement for the model with corners `I`;
this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero

-/

@[expose] public section

open Set
open scoped Topology

-- Let `M` be a manifold with corners over the pair `(E, H)`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in
/-- `p ∈ M` is an interior point of a manifold `M` iff its image in the extended chart
lies in the interior of the model space. -/
def IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

variable (I) in
/-- `p ∈ M` is a boundary point of a manifold `M` iff its image in the extended chart
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

/-- The boundary is the complement of the interior. -/
lemma compl_interior : (I.interior M)ᶜ = I.boundary M:= by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

/-- The interior is the complement of the boundary. -/
lemma compl_boundary : (I.boundary M)ᶜ = I.interior M:= by
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

/-- `M` is boundaryless iff its boundary is empty. -/
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

-- TODO
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
    exact h -- TODO

/-- The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`. -/
lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) ∪ Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.compl_interior, J.compl_interior, union_comm]
  rfl -- TODO

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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace H' N] [ChartedSpace H' N']

open Topology

lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inl x: M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inl x: M ⊕ M') := by
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
  by_contra h
  set x := Sum.getLeft p hleft
  rw [isInteriorPoint_iff_not_isBoundaryPoint x, not_not] at h
  rw [isInteriorPoint_iff_not_isBoundaryPoint p] at hp
  have := boundaryPoint_inl (M' := M') x (by tauto)
  rw [← Sum.eq_left_getLeft_of_isLeft hleft] at this
  exact hp this

lemma isInteriorPoint_disjointUnion_right {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  by_contra h
  set x := Sum.getRight p hright
  rw [← mem_empty_iff_false p, ← (disjoint_interior_boundary (I := I)).inter_eq]
  constructor
  · rw [ModelWithCorners.interior, mem_setOf]; exact hp
  · rw [ModelWithCorners.boundary, mem_setOf, Sum.eq_right_getRight_of_isRight hright]
    have := isInteriorPoint_or_isBoundaryPoint (I := I) x
    exact boundaryPoint_inr (M' := M') x (by tauto)

lemma interior_disjointUnion :
    ModelWithCorners.interior (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.interior (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
  ext p
  constructor
  · intro hp
    by_cases h : Sum.isLeft p
    · left
      exact ⟨Sum.getLeft p h, isInteriorPoint_disjointUnion_left hp h, Sum.inl_getLeft p h⟩
    · replace h := Sum.not_isLeft.mp h
      right
      exact ⟨Sum.getRight p h, isInteriorPoint_disjointUnion_right hp h, Sum.inr_getRight p h⟩
  · intro hp
    by_cases h : Sum.isLeft p
    · set x := Sum.getLeft p h with x_eq
      rw [Sum.eq_left_getLeft_of_isLeft h]
      apply interiorPoint_inl x
      have hp : p ∈ Sum.inl '' (ModelWithCorners.interior (I := I) M) := by
        obtain (good | ⟨y, hy, hxy⟩) := hp
        exacts [good, (not_isLeft_and_isRight ⟨h, by rw [← hxy]; exact rfl⟩).elim]
      obtain ⟨x', hx', hx'p⟩ := hp
      simpa [x_eq, ← hx'p, Sum.getLeft_inl]
    · set x := Sum.getRight p (Sum.not_isLeft.mp h) with x_eq
      rw [Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp h)]
      apply interiorPoint_inr x
      have hp : p ∈ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
        obtain (⟨y, hy, hxy⟩ | good) := hp
        exacts [(not_isLeft_and_isRight ⟨by rw [← hxy]; exact rfl, Sum.not_isLeft.mp h⟩).elim, good]
      obtain ⟨x', hx', hx'p⟩ := hp
      simpa [x_eq, ← hx'p, Sum.getRight_inr]

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
