/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Group.ContinuousInv

/-!
# Basic results on topological groups

This file develops general consequences of the topological-group axioms. It includes the
homeomorphisms given by left and right multiplication, continuity of conjugation, induced and
product topological-group structures, and results about compact sets and connected components.

It also constructs infima of topological-group topologies. Results specifically about inversion,
division, neighbourhoods, integer powers, ordered groups, subgroups, and units are provided by the
corresponding sibling files.

## Tags

topological space, group, topological group
-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

variable {G H α β : Type*}

/-- In a Hausdorff magma with continuous multiplication, the centralizer of any set is closed. -/
lemma Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, ofPred_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
  refine isClosed_imp (by simp) <| isClosed_eq ?_ ?_
  all_goals fun_prop

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/

variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the left in a topological additive group as a homeomorphism. -/]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with }

@[to_additive (attr := simp)]
theorem Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·) :=
  rfl

@[to_additive]
theorem Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ := by
  ext
  rfl

@[to_additive]
lemma isOpenMap_mul_left (a : G) : IsOpenMap (a * ·) := (Homeomorph.mulLeft a).isOpenMap

@[to_additive IsOpen.left_addCoset]
theorem IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (x • U) :=
  isOpenMap_mul_left x _ h

@[to_additive]
lemma isClosedMap_mul_left (a : G) : IsClosedMap (a * ·) := (Homeomorph.mulLeft a).isClosedMap

@[to_additive IsClosed.left_addCoset]
theorem IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (x • U) :=
  isClosedMap_mul_left x _ h

@[to_additive (attr := simp)]
theorem Filter.map_mul_left_nhdsNE {c a : G} :
    map (c * ·) (𝓝[≠] a) = (𝓝[≠] (c * a)) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive /-- Addition from the right in a topological additive group as a homeomorphism. -/]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with }

@[to_additive (attr := simp)]
lemma Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a) := rfl

@[to_additive]
theorem Homeomorph.mulRight_symm (a : G) :
    (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl

@[to_additive]
theorem isOpenMap_mul_right (a : G) : IsOpenMap (· * a) :=
  (Homeomorph.mulRight a).isOpenMap

@[to_additive IsOpen.right_addCoset]
theorem IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (op x • U) :=
  isOpenMap_mul_right x _ h

@[to_additive]
theorem isClosedMap_mul_right (a : G) : IsClosedMap (· * a) :=
  (Homeomorph.mulRight a).isClosedMap

@[to_additive IsClosed.right_addCoset]
theorem IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (op x • U) :=
  isClosedMap_mul_right x _ h

@[to_additive (attr := simp)]
theorem Filter.map_mul_right_nhdsNE {c a : G} :
    map (· * c) (𝓝[≠] a) = (𝓝[≠] (a * c)) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
theorem discreteTopology_iff_isOpen_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  MulAction.IsPretransitive.discreteTopology_iff G 1

@[to_additive]
theorem discreteTopology_of_isOpen_singleton_one (h : IsOpen ({1} : Set G)) :
    DiscreteTopology G :=
  discreteTopology_iff_isOpen_singleton_one.mpr h

@[to_additive]
theorem smul_connectedComponent (g h : G) : g • connectedComponent h = connectedComponent (g * h) :=
  (Homeomorph.mulLeft g).isQuotientMap.image_connectedComponent (by simp [isConnected_singleton]) h

@[to_additive]
theorem totallyDisconnectedSpace_iff_connectedComponent_one :
    TotallyDisconnectedSpace G ↔ connectedComponent (1 : G) = {1} :=
  ⟨fun _ ↦ connectedComponent_eq_singleton 1,
    fun h ↦ totallyDisconnectedSpace_iff_connectedComponent_singleton.mpr fun g ↦ by
      rw [← mul_one g, ← smul_connectedComponent, h, Set.smul_set_singleton, smul_eq_mul]⟩

@[to_additive]
lemma Filter.tendsto_mul_const_iff (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · * b) l (𝓝 (c * b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert! Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]
lemma Filter.tendsto_const_mul_iff (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (b * f ·) l (𝓝 (b * c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert! Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

end ContinuousMulGroup

section IsTopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `x y ↦ x * y⁻¹` (resp., subtraction) is continuous.
-/

section Conj

instance ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] : ContinuousConstSMul (ConjAct Mˣ) M :=
  ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩

open scoped Pointwise in
instance [Group G] [Group H] [TopologicalSpace G] [MulDistribMulAction H G]
    [ContinuousConstSMul H G] {𝒢 : Subgroup G} (h : H) [DiscreteTopology 𝒢] :
    DiscreteTopology ↑(h • 𝒢) := by
  simp only [← SetLike.coe_sort_coe, ← isDiscrete_iff_discreteTopology] at *
  refine IsDiscrete.image_of_isOpenMap ‹_› ?_ fun x y ↦ by simp
  apply IsOpenMap.of_inverse (f' := fun x ↦ h⁻¹ • x) (continuous_const_smul _) <;>
  · intro x
    simp

variable [TopologicalSpace G] [Inv G] [Mul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive continuous_addConj_prod
  /-- Conjugation is jointly continuous on `G × G` when both `add` and `neg` are continuous. -/]
theorem IsTopologicalGroup.continuous_conj_prod [ContinuousMul G] [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation by a fixed element is continuous when `add` is continuous. -/]
theorem IsTopologicalGroup.continuous_conj [SeparatelyContinuousMul G] (g : G) :
    Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_const g⁻¹).comp (continuous_const_mul g)

instance {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G where
  continuous_const_smul h := IsTopologicalGroup.continuous_conj (ConjAct.ofConjAct h)

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation acting on fixed element of the additive group is continuous when both
    `add` and `neg` are continuous. -/]
theorem IsTopologicalGroup.continuous_conj' [ContinuousMul G] [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_const h).mul continuous_inv

end Conj

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace α]

instance : IsTopologicalGroup (ULift G) where

@[to_additive]
instance Prod.instIsTopologicalGroup [TopologicalSpace H] [Group H] [IsTopologicalGroup H] :
    IsTopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prodMap continuous_inv

@[to_additive]
instance OrderDual.instIsTopologicalGroup : IsTopologicalGroup Gᵒᵈ where

@[to_additive]
instance Pi.isTopologicalGroup {C : β → Type*} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, IsTopologicalGroup (C b)] : IsTopologicalGroup (∀ b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias Pi.topologicalGroup := Pi.isTopologicalGroup

@[to_additive]
instance [Inv α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
instance [Group α] [IsTopologicalGroup α] : IsTopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
theorem nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg 𝓝 inv_one)

@[to_additive]
theorem inv_mem_nhds_one {S : Set G} (hS : S ∈ (𝓝 1 : Filter G)) : S⁻¹ ∈ 𝓝 (1 : G) := by
  rwa [← nhds_one_symm'] at hS

set_option backward.defeqAttrib.useBackward true in
/-- The map `(x, y) ↦ (x, x * y)` as a homeomorphism. This is a shear mapping. -/
@[to_additive /-- The map `(x, y) ↦ (x, x + y)` as a homeomorphism. This is a shear mapping. -/]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with }

@[to_additive (attr := simp)]
theorem Homeomorph.shearMulRight_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl

@[to_additive (attr := simp)]
theorem Homeomorph.shearMulRight_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl

variable {G}

@[to_additive]
protected theorem Topology.IsInducing.isTopologicalGroup {F : Type*} [Group H] [TopologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : IsInducing f) : IsTopologicalGroup H :=
  { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive (attr := deprecated (since := "2026-08-21"))]
protected alias Topology.IsInducing.topologicalGroup := Topology.IsInducing.isTopologicalGroup

@[to_additive]
theorem isTopologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) :
    @IsTopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Topology.IsInducing.isTopologicalGroup f ⟨rfl⟩

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_induced := isTopologicalGroup_induced

end IsTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

@[to_additive]
theorem IsTopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variable [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `K + V ⊆ U`. -/]
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
  /-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `V + K ⊆ U`. -/]
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_mono hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
  /-- A compact set is covered by finitely many left additive translates of a set
    with non-empty interior. -/]
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (g * ·) ⁻¹' V := by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    obtain ⟨g₀, hg₀⟩ := hV
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (by fun_prop) ?_
    rwa [mem_preimage, inv_mul_cancel_right]
  exact ⟨t, Subset.trans ht <| iUnion₂_mono fun g _ => interior_subset⟩

/-- Every weakly locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace
  /-- Every weakly locally compact separable topological additive group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/]
instance (priority := 100) SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace [SeparableSpace G]
    [WeaklyLocallyCompactSpace G] : SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨⟨fun n => (fun x => x * denseSeq G n) ⁻¹' L, ?_, ?_⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).isCompact_preimage.mpr hLc
  · refine iUnion_eq_univ_iff.2 fun x => ?_
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (denseSeq G) ∩ (fun y => x * y) ⁻¹' L).Nonempty := by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact (denseRange_denseSeq G).inter_nhds_nonempty
          ((Homeomorph.mulLeft x).continuous.continuousAt <| hL1)
    exact ⟨n, hn⟩

/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
  /-- Given two compact sets in a noncompact additive topological group, there is a
  translate of the second one that is disjoint from the first one. -/]
theorem exists_disjoint_smul_of_isCompact [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
    (hL : IsCompact L) : ∃ g : G, Disjoint K (g • L) := by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : ∃ g, g ∉ K * L⁻¹ := by
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine ⟨g, ?_⟩
  refine disjoint_left.2 fun a ha h'a => hg ?_
  rcases h'a with ⟨b, bL, rfl⟩
  refine ⟨g * b, ha, b⁻¹, by simpa only [Set.mem_inv, inv_inv] using bL, ?_⟩
  simp only [mul_inv_cancel_right]

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsTopologicalAddGroup (Additive G) where
  continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] :
    IsTopologicalGroup (Multiplicative G) where
  continuous_inv := @continuous_neg G _ _ _

section LatticeOps

variable {ι : Sort*} [Group G]

@[to_additive]
theorem isTopologicalGroup_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sInf ts) _ :=
  letI := sInf ts
  { toContinuousInv :=
      @continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ <| h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
        @IsTopologicalGroup.toContinuousMul G t _ <| h t ht }

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_sInf := isTopologicalGroup_sInf

@[to_additive]
theorem isTopologicalGroup_iInf {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @IsTopologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact isTopologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_iInf := isTopologicalGroup_iInf

@[to_additive]
theorem isTopologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGroup G t₁ _)
    (h₂ : @IsTopologicalGroup G t₂ _) : @IsTopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine isTopologicalGroup_iInf fun b => ?_
  cases b <;> assumption

@[to_additive (attr := deprecated (since := "2026-08-21"))]
alias topologicalGroup_inf := isTopologicalGroup_inf

end LatticeOps
