/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.IsManifold
-- TODO: move the smoothness results to a different file, then adjoint this import accordingly!
import Mathlib.Geometry.Manifold.ContMDiffMap

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
- `ModelWithCorners.interior_prod`: the interior of `M × N` is the product of the interiors
of `M` and `N`.
- `ModelWithCorners.boundary_prod`: the boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
- `ModelWithCorners.BoundarylessManifold.prod`: if `M` and `N` are boundaryless, so is `M × N`

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
    fun h ↦ PartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

variable (M) in
/-- The **boundary** of a manifold `M` is the set of its boundary points. -/
protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

lemma isBoundaryPoint_iff {x : M} : I.IsBoundaryPoint x ↔ extChartAt I x x ∈ frontier (range I) :=
  Iff.rfl

/-- Every point is either an interior or a boundary point. -/
lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  rw [IsInteriorPoint, or_iff_not_imp_left, I.isBoundaryPoint_iff, ← closure_diff_interior,
    I.isClosed_range.closure_eq, mem_diff]
  exact fun h => ⟨mem_range_self _, h⟩

/-- A manifold decomposes into interior and boundary. -/
lemma interior_union_boundary_eq_univ : (I.interior M) ∪ (I.boundary M) = (univ : Set M) :=
  eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

/-- The interior and boundary of a manifold `M` are disjoint. -/
lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp (disjoint_interior_frontier (s := range I)), mem_inter_iff]
  exact ⟨h1, h2⟩

/-- The boundary is the complement of the interior. -/
lemma compl_interior : (I.interior M)ᶜ = I.boundary M:= by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp (I.disjoint_interior_boundary)

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
  show x ∈ I.interior M
  rw [← compl_interior, compl_empty_iff] at h
  rw [h]
  trivial

/-- Manifolds with empty boundary are boundaryless. -/
lemma Boundaryless.of_boundary_eq_empty (h : I.boundary M = ∅) : BoundarylessManifold I M :=
  (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

end BoundarylessManifold

/-! Interior and boundary of the product of two manifolds. -/
section prod

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'} {x : M} {y : N}

/-- The interior of `M × N` is the product of the interiors of `M` and `N`. -/
lemma interior_prod :
    (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interior N) := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq, ← Set.range_prod_map, modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint, ← aux] at hp
    exact hp
  · show (I.prod J).IsInteriorPoint p
    rw [IsInteriorPoint, ← aux, mem_prod]
    obtain h := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h
    exact h

/-- The boundary of `M × N` is `∂M × N ∪ (M × ∂N)`. -/
lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) ∪ Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.compl_interior, J.compl_interior, union_comm]
  rfl

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

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}
  [hM : IsManifold I n M] [hM' : IsManifold I n M']
  [Nonempty M] [Nonempty M'] [Nonempty H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : Type*} {J : ModelWithCorners 𝕜 E' H'}
  {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace H' N] [ChartedSpace H' N']
  [IsManifold J n N] [IsManifold J n N'] [Nonempty N] [Nonempty N'] [Nonempty H']

open Topology

lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (@Sum.inl M M' x) := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp only [PartialHomeomorph.extend.eq_1, PartialEquiv.trans_target, toPartialEquiv_coe_symm,
    PartialHomeomorph.lift_openEmbedding_target, PartialEquiv.coe_trans, toPartialEquiv_coe,
    PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.lift_openEmbedding_toFun, Function.comp_apply]
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  rw [I.isInteriorPoint_iff, extChartAt] at hx
  exact hx

lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (@Sum.inl M M' x) := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp only [PartialHomeomorph.extend.eq_1, PartialEquiv.trans_target, toPartialEquiv_coe_symm,
    PartialHomeomorph.lift_openEmbedding_target, PartialEquiv.coe_trans, toPartialEquiv_coe,
    PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.lift_openEmbedding_toFun, Function.comp_apply]
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  rw [I.isBoundaryPoint_iff, extChartAt] at hx
  exact hx

lemma interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (@Sum.inr M M' x) := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp only [PartialHomeomorph.extend.eq_1, PartialEquiv.trans_target, toPartialEquiv_coe_symm,
    PartialHomeomorph.lift_openEmbedding_target, PartialEquiv.coe_trans, toPartialEquiv_coe,
    PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.lift_openEmbedding_toFun, Function.comp_apply]
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  rw [I.isInteriorPoint_iff, extChartAt] at hx
  exact hx

lemma boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (@Sum.inr M M' x) := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp only [PartialHomeomorph.extend.eq_1, PartialEquiv.trans_target, toPartialEquiv_coe_symm,
    PartialHomeomorph.lift_openEmbedding_target, PartialEquiv.coe_trans, toPartialEquiv_coe,
    PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.lift_openEmbedding_toFun, Function.comp_apply]
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  rw [I.isBoundaryPoint_iff, extChartAt] at hx
  exact hx

-- TODO: move to its proper place
lemma not_isLeft_and_isRight {α β : Type*} {x : α ⊕ β} : ¬(x.isLeft ∧ x.isRight) := by
  aesop

-- Converse to the previous direction: if `x` were not an interior point,
-- it had to be a boundary point, hence `p` were a boundary point also, contradiction.
lemma isInteriorPoint_disjointUnion_left {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft) := by
  by_contra h
  set x := Sum.getLeft p hleft
  rw [← mem_empty_iff_false p, ← (disjoint_interior_boundary (I := I) (M := M ⊕ M')).inter_eq]
  constructor
  · rw [ModelWithCorners.interior, mem_setOf]; exact hp
  · rw [ModelWithCorners.boundary, mem_setOf, Sum.eq_left_getLeft_of_isLeft hleft]
    have aux := isInteriorPoint_or_isBoundaryPoint (I := I) x
    apply boundaryPoint_inl (M' := M') x; tauto

lemma isInteriorPoint_disjointUnion_right {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  by_contra h
  set x := Sum.getRight p hright
  rw [← mem_empty_iff_false p, ← (disjoint_interior_boundary (I := I) (M := M ⊕ M')).inter_eq]
  constructor
  · rw [ModelWithCorners.interior, mem_setOf]; exact hp
  · rw [ModelWithCorners.boundary, mem_setOf, Sum.eq_right_getRight_of_isRight hright]
    have aux := isInteriorPoint_or_isBoundaryPoint (I := I) x
    apply boundaryPoint_inr (M' := M') x; tauto

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
    · right
      exact ⟨Sum.getRight p ((Sum.not_isLeft.mp h)),
        isInteriorPoint_disjointUnion_right hp (Sum.not_isLeft.mp h),
        Sum.inr_getRight p (Sum.not_isLeft.mp h)⟩
  · intro hp
    rw [ModelWithCorners.interior, mem_setOf]
    by_cases h : Sum.isLeft p
    · set x := Sum.getLeft p h with x_eq
      rw [Sum.eq_left_getLeft_of_isLeft h]
      apply interiorPoint_inl x
      have hp : p ∈ Sum.inl '' (ModelWithCorners.interior (I := I) M) := by
        obtain (good | ⟨y, hy, hxy⟩) := hp
        exacts [good, (not_isLeft_and_isRight ⟨h, by rw [← hxy]; exact rfl⟩).elim]
      obtain ⟨x', hx', hx'p⟩ := hp
      simp_rw [x_eq, ← hx'p, Sum.getLeft_inl]
      exact hx'
    · set x := Sum.getRight p (Sum.not_isLeft.mp h) with x_eq
      rw [Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp h)]
      apply interiorPoint_inr x
      have hp : p ∈ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
        obtain (⟨y, hy, hxy⟩ | good) := hp
        exacts [(not_isLeft_and_isRight ⟨by rw [← hxy]; exact rfl, Sum.not_isLeft.mp h⟩).elim, good]
      obtain ⟨x', hx', hx'p⟩ := hp
      simp_rw [x_eq, ← hx'p, Sum.getRight_inr]
      exact hx'

-- TODO: name and move to the right place
lemma foo {α β : Type*} {s : Set α} {t : Set β} :
    (Sum.inl '' s ∪ Sum.inr '' t)ᶜ = Sum.inl '' sᶜ ∪ Sum.inr '' tᶜ := by
  rw [compl_union]
  aesop

lemma boundary_disjointUnion : ModelWithCorners.boundary (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.boundary (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.boundary (I := I) M') := by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, foo]

/-- If `M` and `M'` are boundaryless, so is their disjoint union `M ⊔ M'`. -/
instance boundaryless_disjointUnion
    [hM: BoundarylessManifold I M] [hM': BoundarylessManifold I M'] :
    BoundarylessManifold I (M ⊕ M') := by
  rw [← Boundaryless.iff_boundary_eq_empty] at hM
  rw [← Boundaryless.iff_boundary_eq_empty] at hM'
  simp [← Boundaryless.iff_boundary_eq_empty, boundary_disjointUnion, hM, hM']

lemma ContMDiff.inl : ContMDiff I I n (@Sum.inl M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inl.continuousAt, ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sum_chartAt_inl]
    congr
    apply Sum.inl_injective.extend_apply (chartAt _ x)

  -- key step: fns are eventually equal
  set C := chartAt H x
  have aux₁ : ∀ x ∈ I.symm ⁻¹' C.target ∩ range I,
      (((C.lift_openEmbedding (IsOpenEmbedding.inl (Y := M'))).extend I)
        ∘ Sum.inl ∘ (C.extend I).symm) x = x := by
    intro x ⟨hx1, hx2⟩
    simp [Sum.inl_injective.extend_apply C, C.right_inv hx1, I.right_inv hx2]

  -- can be cleaned up, but works
  have : (extChartAt I x) x ∈ I.symm ⁻¹' C.target ∩ range I := by
      simp only [extChartAt, C]
      dsimp
      constructor--; swap
      swap; · exact mem_range_self _
      rw [mem_preimage]
      set C := chartAt H x
      have : C x ∈ C.target := by exact mem_chart_target H x
      convert this
      set y := C x
      apply I.left_inv'
      rw [I.source_eq]; exact trivial

  have aux₂ : (I.symm ⁻¹' C.target ∩ range I) ∈ 𝓝[range I] ((extChartAt I x) x) := by
    rw [extChartAt]
    set C' := chartAt H x
    rw [← PartialHomeomorph.map_extend_nhds _ (ChartedSpace.mem_chart_source x)]
    sorry
    -- rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    -- use I.symm ⁻¹' C.target
    -- constructor; swap; · simp
    -- sorry -- is I.symm ⁻¹' C.target a nbhd of (extChartAt I x) x? is it open enough?
  apply Filter.mem_of_superset aux₂ aux₁

  -- simp only [extChartAt, ChartedSpace.sum_chartAt_inl]
  -- set C := chartAt H x
  -- use (I.symm ⁻¹' C.target)
  -- constructor
  -- · sorry
  -- · use (range I), by simp
  --   ext x
  --   constructor
  --   · intro hx
  --     -- rw [mem_setOf] at hx
  --     dsimp at hx
  --     rw [Sum.inl_injective.extend_apply C] at hx
  --     -- probably too strong...
  --     sorry
  --   · exact fun hx ↦ asdf x hx


  /- simp only [extChartAt, ChartedSpace.sum_chartAt_inl, PartialHomeomorph.lift_openEmbedding,
    PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm,
    PartialHomeomorph.extend.eq_1, PartialEquiv.coe_trans]
  set C := chartAt H x
  -- I is not an issue; C is!
  have : EqOn (I ∘ I.symm) id (range I) := fun x hx ↦ I.right_inv hx
  have : EqOn (I ∘ C ∘ C.symm ∘ I.symm) id (range I) := by
    have : I.symm '' (range I) ⊆ C.target := by
      intro x' hx'
      sorry
  have : ContDiffWithinAt 𝕜 n (I ∘ C ∘ C.symm ∘ I.symm) (range I) (I (C x)) := by
    -- TODO! idea. near I (C x), C and I have their inverses, so this is locally just id
    have : C ∘ C.symm = id := by
      ext x
      apply C.right_inv'
      sorry -- is x ∈ C.target?
    have := calc I ∘ ↑C ∘ ↑C.symm ∘ ↑I.symm
      _ = I ∘ (C ∘ C.symm) ∘ I.symm := by simp only [Function.comp_assoc]
      _ = I ∘ id ∘ I.symm := by rw [this]
      _ = I ∘ I.symm := by simp
      _ = id := by
        ext x
        dsimp
        have : I.symm x ∈ I.source := sorry
        apply I.right_inv'
        sorry
    rw [this]; sorry
  apply ContDiffWithinAt.congr this
  · intro y hy
    dsimp only [Function.comp_apply]
    congr
    apply Sum.inl_injective.extend_apply C
  · dsimp only [Function.comp_apply]
    congr
    apply Sum.inl_injective.extend_apply -/

  -- write in charts at x and inl x; then expand the charts there
  -- finally, the statement should boil down to lift_openEmbedding being nice...

-- TODO: add the analogous argument, once the lemma above is proven
lemma ContMDiff.inr : ContMDiff I I n (@Sum.inr M M') := by sorry

-- TODO: two more lemmas to prove
lemma ContMDiff.sum_elim {f : M → N} {g : M' → N}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g) := by

  intro p
  rw [contMDiffAt_iff]
  refine ⟨(Continuous.sum_elim hf.continuous hg.continuous).continuousAt, ?_⟩

  by_cases h: p.isLeft
  · set x := Sum.getLeft p h
    have : p = Sum.inl x := Sum.eq_left_getLeft_of_isLeft h
    rw [this]
    simp only [extChartAt, ChartedSpace.sum_chartAt_inl]
    set C := chartAt H x
    set F := Sum.elim f g
    --rw [← this]
    unfold F
    dsimp
    rw [Sum.inl_injective.extend_apply C]
    -- now: Sum.elim combined with Sum.inl simplifies to f, then it's smoothness of f
    -- similarly for g
    apply ContDiffWithinAt.congr_of_eventuallyEq
    · sorry  -- diff of the fn I want; what's f?
    · sorry  -- fns equally eventually near p
    · sorry
      --simp only [extChartAt]
      --simp only [ChartedSpace.sum_chartAt_inl]
      --set C := chartAt H x
      --rw [ChartedSpace.sum_chartAt_inl]


    sorry
      --simp [ChartedSpace.sum_chartAt_inl]
      --congr
      --apply Sum.inl_injective.extend_apply (chartAt _ x)

    --sorry
  sorry

lemma ContMDiff.sum_map {f : M → N} {g : M' → N'}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.map f g) :=
  ContMDiff.sum_elim (ContMDiff.inl.comp hf) (ContMDiff.inr.comp hg)

-- in fact, have an iff, but the other direction is easy :-)
lemma bar {f : M → N} (h : ContMDiff I J n ((@Sum.inl N N') ∘ f)) : ContMDiff I J n f := by
  let anything : N := sorry
  let aux : N ⊕ N' → N := Sum.elim (@id N) (fun _ ↦ anything)
  have haux : ContMDiffOn J J n aux (Sum.inl '' univ) :=
    (ContMDiff.sum_elim contMDiff_id contMDiff_const).contMDiffOn
  rw [← contMDiffOn_univ] at h ⊢
  have : f = aux ∘ (@Sum.inl N N') ∘ f := by simp only [aux, Function.comp_apply]; rfl
  rw [this]
  have : univ ⊆ (Sum.inl ∘ f) ⁻¹' (@Sum.inl N N' '' univ) := by
    intro x _hx
    rw [mem_preimage, Function.comp_apply]
    use f x, trivial
  exact ContMDiffOn.comp haux h this

-- in fact, have an iff, but the other direction is easy :-)
lemma baz {g : M' → N'} (h : ContMDiff I J n ((@Sum.inr N N') ∘ g)) : ContMDiff I J n g := by
  let anything : N' := sorry
  let aux : N ⊕ N' → N' := Sum.elim (fun _ ↦ anything) (@id N')
  have haux : ContMDiffOn J J n aux (Sum.inr '' univ) :=
    (ContMDiff.sum_elim contMDiff_const contMDiff_id).contMDiffOn
  rw [← contMDiffOn_univ] at h ⊢
  have : g = aux ∘ (@Sum.inr N N') ∘ g := by simp only [aux, Function.comp_apply]; rfl
  rw [this]
  apply ContMDiffOn.comp haux h
  intro x _hx
  rw [mem_preimage, Function.comp_apply]
  use g x, trivial

lemma contMDiff_sum_map {f : M → N} {g : M' → N'} :
    ContMDiff I J n (Sum.map f g) ↔ ContMDiff I J n f ∧ ContMDiff I J n g :=
  ⟨fun h ↦ ⟨bar (h.comp ContMDiff.inl), baz (h.comp ContMDiff.inr)⟩,
    fun h ↦ ContMDiff.sum_map h.1 h.2⟩

-- my bordism theory branch has a bunch of corollaries about diffeomorphisms now

lemma ContMDiff.swap : ContMDiff I I n (@Sum.swap M M') := ContMDiff.sum_elim inr inl

end disjointUnion

end ModelWithCorners
