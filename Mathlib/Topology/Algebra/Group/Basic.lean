/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.Bases.Finite
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological groups

This file defines the following typeclasses:

* `IsTopologicalGroup`, `IsTopologicalAddGroup`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `ContinuousSub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `ContinuousSub` from `IsTopologicalGroup` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `Homeomorph` versions of several `Equiv`s: `Homeomorph.mulLeft`,
`Homeomorph.mulRight`, `Homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

/-- In a Hausdorff magma with continuous multiplication, the centralizer of any set is closed. -/
lemma Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, setOf_forall]
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
  convert (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
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
  convert (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
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
  convert Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]
lemma Filter.tendsto_const_mul_iff (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (b * f ·) l (𝓝 (b * c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

end ContinuousMulGroup

/-!
### `ContinuousInv` and `ContinuousNeg`
-/

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

@[to_additive]
theorem ContinuousInv.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Group α]
    [DivisionMonoid β] [MonoidHomClass F α β] [tβ : TopologicalSpace β] [ContinuousInv β] (f : F) :
    @ContinuousInv α (tβ.induced f) _ := by
  let _tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_inv]
  fun_prop

@[to_additive]
protected theorem Specializes.inv {x y : G} (h : x ⤳ y) : (x⁻¹) ⤳ (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
protected theorem Inseparable.inv {x y : G} (h : Inseparable x y) : Inseparable (x⁻¹) (y⁻¹) :=
  h.map continuous_inv

@[to_additive]
protected theorem Specializes.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : x ⤳ y) : ∀ m : ℤ, (x ^ m) ⤳ (y ^ m)
  | .ofNat n => by simpa using h.pow n
  | .negSucc n => by simpa using (h.pow (n + 1)).inv

@[to_additive]
protected theorem Inseparable.zpow {G : Type*} [DivInvMonoid G] [TopologicalSpace G]
    [ContinuousMul G] [ContinuousInv G] {x y : G} (h : Inseparable x y) (m : ℤ) :
    Inseparable (x ^ m) (y ^ m) :=
  (h.specializes.zpow m).antisymm (h.specializes'.zpow m)

@[to_additive]
instance : ContinuousInv (ULift G) :=
  ⟨continuous_uliftUp.comp (continuous_inv.comp continuous_uliftDown)⟩

@[to_additive]
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.continuousOn

@[to_additive]
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.continuousWithinAt

@[to_additive]
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.continuousAt

@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive]
instance OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ := ‹ContinuousInv G›

@[to_additive]
instance Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] :
    ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prodMk continuous_inv.snd'⟩

variable {ι : Type*}

@[to_additive]
instance Pi.continuousInv {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, ContinuousInv (C i)] : ContinuousInv (∀ i, C i) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

/-- A version of `Pi.continuousInv` for non-dependent functions. It is needed because sometimes
Lean fails to use `Pi.continuousInv` for non-dependent functions. -/
@[to_additive
  /-- A version of `Pi.continuousNeg` for non-dependent functions. It is needed
  because sometimes Lean fails to use `Pi.continuousNeg` for non-dependent functions. -/]
instance Pi.has_continuous_inv' : ContinuousInv (ι → G) :=
  Pi.continuousInv

@[to_additive]
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousInv_of_indiscreteTopology [TopologicalSpace H] [Inv H]
    [IndiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_discreteTopology [TopologicalSpace H] [Div H]
    [DiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousDiv_of_indiscreteTopology [TopologicalSpace H] [Div H]
    [IndiscreteTopology H] : ContinuousDiv H :=
  ⟨continuous_of_indiscreteTopology⟩

@[to_additive]
instance (priority := 100) topologicalGroup_of_discreteTopology
    [TopologicalSpace H] [Group H] [DiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

@[to_additive]
instance (priority := 100) topologicalGroup_of_indiscreteTopology
    [TopologicalSpace H] [Group H] [IndiscreteTopology H] : IsTopologicalGroup H := ⟨⟩

section PointwiseLimits

variable (G₁ G₂ : Type*) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
theorem isClosed_setOf_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv

end PointwiseLimits

instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  continuous_neg := @continuous_inv H _ _ _

instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

@[to_additive (attr := simp)]
theorem tendsto_inv_iff {l : Filter α} {m : α → G} {a : G} :
    Tendsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, Tendsto.inv⟩

@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv_eq_inv]
  exact hs.image continuous_inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive /-- Negation in a topological group as a homeomorphism. -/]
protected def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with }

@[to_additive (attr := simp)]
lemma Homeomorph.symm_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    (Homeomorph.inv G).symm = Homeomorph.inv G := rfl

@[to_additive (attr := simp)]
lemma Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    ⇑(Homeomorph.inv G) = Inv.inv := rfl

@[to_additive]
theorem nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹ :=
  ((Homeomorph.inv G).map_nhds_eq a).symm

@[to_additive]
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isOpenMap

@[to_additive]
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isClosedMap

variable {G}

@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.preimage continuous_inv

@[to_additive]
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive (attr := simp)]
lemma continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f := (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]
lemma continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x :=
  (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]
lemma continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s :=
  (Homeomorph.inv G).comp_continuousOn_iff _ _

@[to_additive] alias ⟨Continuous.of_inv, _⟩ := continuous_inv_iff
@[to_additive] alias ⟨ContinuousAt.of_inv, _⟩ := continuousAt_inv_iff
@[to_additive] alias ⟨ContinuousOn.of_inv, _⟩ := continuousOn_inv_iff

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsNE {a : G} : (𝓝[≠] a)⁻¹ = (𝓝[≠] (a⁻¹)) := by
  convert (Homeomorph.inv G).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort*} [Inv G]

@[to_additive]
theorem continuousInv_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @ContinuousInv G t _) : @ContinuousInv G (sInf ts) _ :=
  letI := sInf ts
  { continuous_inv :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom ht (@ContinuousInv.continuous_inv G t _ (h t ht)) }

@[to_additive]
theorem continuousInv_iInf {ts' : ι' → TopologicalSpace G}
    (h' : ∀ i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

@[to_additive]
theorem Topology.IsInducing.continuousInv {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G → H} (hf : IsInducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [Function.comp_def, hf_inv] using hf.continuous.inv⟩

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

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Conjugation acting on fixed element of the additive group is continuous when both
    `add` and `neg` are continuous. -/]
theorem IsTopologicalGroup.continuous_conj' [ContinuousMul G] [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_const h).mul continuous_inv

end Conj

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace α] {f : α → G}
  {s : Set α} {x : α}

instance : IsTopologicalGroup (ULift G) where

section ZPow

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | Int.negSucc n => by simpa using (continuous_pow (n + 1)).inv

instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousConstSMul ℤ A :=
  ⟨continuous_zsmul⟩

instance AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : ContinuousSMul ℤ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z :=
  (continuous_zpow z).comp h

@[to_additive]
theorem continuousOn_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).continuousOn

@[to_additive]
theorem continuousAt_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).continuousAt

@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).tendsto.comp hf

@[to_additive]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (fun x => f x ^ z) s x :=
  Filter.Tendsto.zpow hf z

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (fun x => f x ^ z) x :=
  Filter.Tendsto.zpow hf z

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (fun x => f x ^ z) s := fun x hx => (hf x hx).zpow z

end ZPow

section OrderedCommGroup

variable [TopologicalSpace H] [CommGroup H] [PartialOrder H] [IsOrderedMonoid H]

section mul

variable [ContinuousMul H]

@[to_additive (attr := simp)]
theorem Filter.map_mul_left_nhdsGT {c a : H} : map (c * ·) (𝓝[>] a) = (𝓝[>] (c * a)) := by
  convert (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
theorem Filter.map_mul_left_nhdsLT {c a : H} : map (c * ·) (𝓝[<] a) = (𝓝[<] (c * a)) := by
  convert (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
theorem Filter.map_mul_right_nhdsGT {c a : H} : map (· * c) (𝓝[>] a) = (𝓝[>] (a * c)) := by
  convert (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.map_mul_right_nhdsLT {c a : H} : map (· * c) (𝓝[<] a) = (𝓝[<] (a * c)) := by
  convert (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end mul

section inv

variable [ContinuousInv H]

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsGT {a : H} : (𝓝[>] a)⁻¹ = (𝓝[<] (a⁻¹)) := by
  convert (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsLT {a : H} : (𝓝[<] a)⁻¹ = (𝓝[>] (a⁻¹)) := by
  convert (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
theorem tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsGT_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsLT_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsGE_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsLE_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

end inv

end OrderedCommGroup

@[to_additive]
instance Prod.instIsTopologicalGroup [TopologicalSpace H] [Group H] [IsTopologicalGroup H] :
    IsTopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prodMap continuous_inv

@[to_additive]
instance OrderDual.instIsTopologicalGroup : IsTopologicalGroup Gᵒᵈ where

@[to_additive]
instance Pi.topologicalGroup {C : β → Type*} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, IsTopologicalGroup (C b)] : IsTopologicalGroup (∀ b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv

open MulOpposite

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
protected theorem Topology.IsInducing.topologicalGroup {F : Type*} [Group H] [TopologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : IsInducing f) : IsTopologicalGroup H :=
  { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }

@[to_additive]
theorem topologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) :
    @IsTopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.topologicalGroup f ⟨rfl⟩

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : IsTopologicalGroup S :=
  IsInducing.subtypeVal.topologicalGroup S.subtype

end Subgroup

/-- The (topological-space) closure of a subgroup of a topological group is
itself a subgroup. -/
@[to_additive
  /-- The (topological-space) closure of an additive subgroup of an additive topological group is
  itself an additive subgroup. -/]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }

@[to_additive (attr := simp)]
theorem Subgroup.topologicalClosure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = _root_.closure s :=
  rfl

@[to_additive]
theorem Subgroup.le_topologicalClosure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
theorem Subgroup.isClosed_topologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := isClosed_closure

@[to_additive]
theorem Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[to_additive (attr := gcongr)]
theorem Subgroup.topologicalClosure_mono {s t : Subgroup G} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

@[to_additive]
theorem DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {f : G →* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs

/-- The topological closure of a normal subgroup is normal. -/
@[to_additive /-- The topological closure of a normal additive subgroup is normal. -/]
theorem Subgroup.is_normal_topologicalClosure {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    (Subgroup.topologicalClosure N).Normal where
  conj_mem n hn g := by
    apply map_mem_closure (IsTopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g

@[to_additive]
theorem mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) := by
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent

@[to_additive]
theorem inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [DivisionMonoid G]
    [ContinuousInv G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive /-- The connected component of 0 is a subgroup of `G`. -/]
def Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg

/-- If a subgroup of a topological group is commutative, then so is its topological closure.

See note [reducible non-instances]. -/
@[to_additive
  /-- If a subgroup of an additive topological group is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
abbrev Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

variable (G) in
@[to_additive]
lemma Subgroup.coe_topologicalClosure_bot :
    ((⊥ : Subgroup G).topologicalClosure : Set G) = _root_.closure ({1} : Set G) := by simp

@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v / w ∈ s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuousAt_fst.mul continuousAt_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp

@[to_additive]
theorem nhds_translation_inv_mul (x : G) : comap (x⁻¹ * ·) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulLeft x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (x⁻¹⁻¹ * 1) = 𝓝 x by simp

@[to_additive (attr := simp)]
theorem map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x := by simp

@[to_additive (attr := simp)]
theorem map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y

@[to_additive]
theorem map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
theorem Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι → Prop} {s : ι → Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) :
    HasBasis (𝓝 x) p fun i => { y | y / x ∈ s i } := by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _

@[to_additive]
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x ∈ closure s ↔ ∀ U ∈ (𝓝 1 : Filter G), ∃ y ∈ s, y / x ∈ U := by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_setOf, id]

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`)
from a topological group to a topological monoid is continuous
provided that it is continuous at one.

This version assumes that `f x → 1` as `x → 1`,
saving a rewrite of `f 1 = 1` compared to `continuous_of_continuousAt_one` in some cases.
See also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero.

  This version assumes that `f x → 0` as `x → 0`,
  saving a rewrite of `f 0 = 0` compared to `continuous_of_continuousAt_zero` in some cases.
  See also `uniformContinuous_of_continuousAt_zero`. -/]
theorem continuous_of_tendsto_nhds_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : Tendsto f (𝓝 1) (𝓝 1)) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x ↦ by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, Function.comp_def,
      map_mul, mul_one] using hf.const_mul (f x)

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  /-- An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero. See also
  `uniformContinuous_of_continuousAt_zero`. -/]
theorem continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : ContinuousAt f 1) :
    Continuous f :=
  continuous_of_tendsto_nhds_one f <| by simpa using hf.tendsto

@[to_additive continuous_of_continuousAt_zero₂]
theorem continuous_of_continuousAt_one₂ {H M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H →* M)
    (hf : ContinuousAt (fun x : G × H ↦ f x.1 x.2) (1, 1))
    (hl : ∀ x, ContinuousAt (f x) 1) (hr : ∀ y, ContinuousAt (f · y) 1) :
    Continuous (fun x : G × H ↦ f x.1 x.2) := continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, Function.comp_def, map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]
lemma IsTopologicalGroup.isInducing_iff_nhds_one
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {F : Type*}
    [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    Topology.IsInducing f ↔ 𝓝 (1 : G) = (𝓝 (1 : H)).comap f := by
  rw [Topology.isInducing_iff_nhds]
  refine ⟨(map_one f ▸ · 1), fun hf x ↦ ?_⟩
  rw [← nhds_translation_mul_inv, ← nhds_translation_mul_inv (f x), Filter.comap_comap, hf,
    Filter.comap_comap]
  congr 1
  ext; simp

@[to_additive]
lemma IsTopologicalGroup.isOpenMap_iff_nhds_one
    {H : Type*} [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H H]
    {F : Type*} [FunLike F G H] [MonoidHomClass F G H] {f : F} :
    IsOpenMap f ↔ 𝓝 1 ≤ .map f (𝓝 1) := by
  refine ⟨fun H ↦ map_one f ▸ H.nhds_le 1, fun h ↦ IsOpenMap.of_nhds_le fun x ↦ ?_⟩
  have : Filter.map (f x * ·) (𝓝 1) = 𝓝 (f x) := by
    simpa [-Homeomorph.map_nhds_eq, Units.smul_def] using
      (Homeomorph.smul ((toUnits x).map (MonoidHomClass.toMonoidHom f))).map_nhds_eq (1 : H)
  rw [← map_mul_left_nhds_one x, Filter.map_map, Function.comp_def, ← this]
  refine (Filter.map_mono h).trans ?_
  simp [Function.comp_def]

-- TODO: unify with `QuotientGroup.isOpenQuotientMap_mk`
/-- Let `A` and `B` be topological groups, and let `φ : A → B` be a continuous surjective group
homomorphism. Assume furthermore that `φ` is a quotient map (i.e., `V ⊆ B`
is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an open map. -/
@[to_additive /-- Let `A` and `B` be topological additive groups, and let `φ : A → B` be a
continuous surjective additive group homomorphism. Assume furthermore that `φ` is a quotient map
(i.e., `V ⊆ B` is open iff `φ⁻¹ V` is open). Then `φ` is an open quotient map, and in particular an
open map. -/]
lemma MonoidHom.isOpenQuotientMap_of_isQuotientMap {A : Type*} [Group A]
    [TopologicalSpace A] [ContinuousMul A] {B : Type*} [Group B] [TopologicalSpace B]
    {F : Type*} [FunLike F A B] [MonoidHomClass F A B] {φ : F}
    (hφ : IsQuotientMap φ) : IsOpenQuotientMap φ where
    surjective := hφ.surjective
    continuous := hφ.continuous
    isOpenMap := by
      -- We need to check that if `U ⊆ A` is open then `φ⁻¹ (φ U)` is open.
      intro U hU
      rw [← hφ.isOpen_preimage]
      -- It suffices to show that `φ⁻¹ (φ U) = ⋃ (U * k⁻¹)` as `k` runs through the kernel of `φ`,
      -- as `U * k⁻¹` is open because `x ↦ x * k` is continuous.
      -- Remark: here is where we use that we have groups not monoids (you cannot avoid
      -- using both `k` and `k⁻¹` at this point).
      suffices ⇑φ ⁻¹' (⇑φ '' U) = ⋃ k ∈ ker (φ : A →* B), (fun x ↦ x * k) ⁻¹' U by
        exact this ▸ isOpen_biUnion (fun k _ ↦ Continuous.isOpen_preimage (by fun_prop) _ hU)
      ext x
      -- But this is an elementary calculation.
      constructor
      · rintro ⟨y, hyU, hyx⟩
        apply Set.mem_iUnion_of_mem (x⁻¹ * y)
        simp_all
      · rintro ⟨_, ⟨k, rfl⟩, _, ⟨(hk : φ k = 1), rfl⟩, hx⟩
        use x * k, hx
        rw [map_mul, hk, mul_one]

@[to_additive]
theorem IsTopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  TopologicalSpace.ext_nhds fun x ↦ by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]

@[to_additive]
theorem IsTopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @IsTopologicalGroup G t _) (tg' : @IsTopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩

@[to_additive]
theorem ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, Function.comp_def, mul_assoc,
    mul_inv_rev, inv_mul_cancel_left] using this

@[to_additive]
theorem IsTopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : IsTopologicalGroup G :=
  { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl, ←
              map_map, ← hleft, hright, map_map]
            simp) }

@[to_additive]
theorem IsTopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : IsTopologicalGroup G := by
  refine IsTopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : ∀ x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [Function.comp_def] using hleft _

@[to_additive]
theorem IsTopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1)) : IsTopologicalGroup G :=
  IsTopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)

variable (G) in
/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → Set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`QuotientGroup.completeSpace_right`. -/
@[to_additive
  /-- Any first countable topological additive group has an antitone neighborhood basis
  `u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`.
  The existence of such a neighborhood basis is a key tool
  for `QuotientAddGroup.completeSpace_right`. -/]
theorem IsTopologicalGroup.exists_antitone_basis_nhds_one [FirstCountableTopology G] :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n := by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in atTop, u m * u m ⊆ u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩

end IsTopologicalGroup

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub_const]
theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds

lemma Filter.tendsto_div_const_iff {G : Type*}
    [GroupWithZero G] [TopologicalSpace G] [ContinuousDiv G]
    {b : G} (hb : b ≠ 0) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel₀ hb, div_one]

@[to_additive tendsto_sub_const_iff]
lemma Filter.tendsto_div_const_iff' {G : Type*}
    [TopologicalSpace G] [Group G] [ContinuousDiv G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[to_additive (attr := continuity) continuous_sub_left]
lemma continuous_div_left' (a : G) : Continuous (a / ·) := by fun_prop

@[to_additive (attr := continuity) continuous_sub_right]
lemma continuous_div_right' (a : G) : Continuous (· / a) := by fun_prop

end ContinuousDiv

section DivInvTopologicalGroup

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive tendsto_const_sub_iff]
lemma Filter.tendsto_const_div_iff' (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (fun k : α ↦ b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, Filter.Tendsto.const_div' b⟩
  convert h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]

@[deprecated (since := "2026-02-03")]
alias Filter.tendsto_const_div_iff := Filter.tendsto_const_div_iff'


/-- A version of `Homeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addLeft a (-b)` that is defeq to `a - b`. -/]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with }

@[to_additive]
theorem isOpenMap_div_left (a : G) : IsOpenMap (a / ·) :=
  (Homeomorph.divLeft _).isOpenMap

@[to_additive]
theorem isClosedMap_div_left (a : G) : IsClosedMap (a / ·) :=
  (Homeomorph.divLeft _).isClosedMap

/-- A version of `Homeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addRight (-a) b` that is defeq to `b - a`. -/]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with }

@[to_additive]
lemma isOpenMap_div_right (a : G) : IsOpenMap (· / a) := (Homeomorph.divRight a).isOpenMap

@[to_additive]
lemma isClosedMap_div_right (a : G) : IsClosedMap (· / a) := (Homeomorph.divRight a).isClosedMap

@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩

@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

end DivInvTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

@[to_additive]
theorem IsTopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

variable (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.) -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly
  discontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact
  `K`. (See also `DiscreteTopology`.) -/]
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simp only [image_smul, mem_setOf_eq, coe_subtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_nonempty_iff' }

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.)

If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousSMul_of_t2Space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
  /-- A subgroup `S` of an additive topological group `G` acts on `G` properly discontinuously
  on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact `K`.
  (See also `DiscreteTopology`.)

  If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousVAdd_of_t2Space`
  to show that the quotient group `G ⧸ S` is Hausdorff. -/]
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S.op G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prodMap continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coe_subtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert H using 1
      ext x
      simp only [image_smul, mem_setOf_eq, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_nonempty_iff }

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

open MulOpposite

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

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x, ← map_mul_right_nhds_one y, ← map₂_mul, map₂_map_left,
        map₂_map_right]

/-- On a topological group, `𝓝 : G → Filter G` can be promoted to a `MulHom`. -/
@[to_additive (attr := simps)
  /-- On an additive topological group, `𝓝 : G → Filter G` can be promoted to an `AddHom`. -/]
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsTopologicalAddGroup (Additive G) where
  continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] :
    IsTopologicalGroup (Multiplicative G) where
  continuous_inv := @continuous_neg G _ _ _

/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive /-- If `G` is an additive group with topological negation, then it is homeomorphic to
its additive units. -/]
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩

@[to_additive] theorem Units.isEmbedding_val [Group G] [TopologicalSpace G] [ContinuousInv G] :
    IsEmbedding (val : Gˣ → G) :=
  toUnits_homeomorph.symm.isEmbedding

lemma Continuous.of_coeHom_comp [Group G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousInv G] {f : G →* Hˣ} (hf : Continuous ((Units.coeHom H).comp f)) : Continuous f := by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

namespace Units

open MulOpposite (continuous_op continuous_unop)

@[to_additive]
theorem range_embedProduct [Monoid α] :
    Set.range (embedProduct α) = {p : α × αᵐᵒᵖ | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} :=
  Set.range_eq_iff _ _ |>.mpr
    ⟨fun a ↦ ⟨a.mul_inv, a.inv_mul⟩, fun p hp ↦ ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
instance [ContinuousMul α] : IsTopologicalGroup αˣ where
  continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]
theorem isClosedEmbedding_embedProduct [T1Space α] [ContinuousMul α] :
    IsClosedEmbedding (embedProduct α) where
  toIsEmbedding := isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop

@[to_additive]
instance [T1Space α] [ContinuousMul α] [CompactSpace α] : CompactSpace αˣ :=
  isClosedEmbedding_embedProduct.compactSpace

@[to_additive]
instance [T1Space α] [ContinuousMul α] [WeaklyLocallyCompactSpace α] :
    WeaklyLocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]
instance [T1Space α] [ContinuousMul α] [LocallyCompactSpace α] : LocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.locallyCompactSpace

lemma _root_.Submonoid.units_isCompact [T1Space α] [ContinuousMul α] {S : Submonoid α}
    (hS : IsCompact (S : Set α)) : IsCompact (S.units : Set αˣ) := by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive prodAddUnits
  /-- The topological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid. -/]
def _root_.Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

end Units

section LatticeOps

variable {ι : Sort*} [Group G]

@[to_additive]
theorem topologicalGroup_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @IsTopologicalGroup G t _) : @IsTopologicalGroup G (sInf ts) _ :=
  letI := sInf ts
  { toContinuousInv :=
      @continuousInv_sInf _ _ _ fun t ht => @IsTopologicalGroup.toContinuousInv G t _ <| h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
        @IsTopologicalGroup.toContinuousMul G t _ <| h t ht }

@[to_additive]
theorem topologicalGroup_iInf {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @IsTopologicalGroup G (ts' i) _) : @IsTopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @IsTopologicalGroup G t₁ _)
    (h₂ : @IsTopologicalGroup G t₂ _) : @IsTopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps
