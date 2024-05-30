/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Constructions

#align_import topology.algebra.group.basic from "leanprover-community/mathlib"@"3b1890e71632be9e3b2086ab512c3259a7e9a3ef"

/-!
# Topological groups

This file defines the following typeclasses:

* `TopologicalGroup`, `TopologicalAddGroup`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `ContinuousSub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `ContinuousSub` from `TopologicalGroup` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `Homeomorph` versions of several `Equiv`s: `Homeomorph.mulLeft`,
`Homeomorph.mulRight`, `Homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/


open scoped Classical
open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Group G] [ContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }
#align homeomorph.mul_left Homeomorph.mulLeft
#align homeomorph.add_left Homeomorph.addLeft

@[to_additive (attr := simp)]
theorem Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·) :=
  rfl
#align homeomorph.coe_mul_left Homeomorph.coe_mulLeft
#align homeomorph.coe_add_left Homeomorph.coe_addLeft

@[to_additive]
theorem Homeomorph.mulLeft_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ := by
  ext
  rfl
#align homeomorph.mul_left_symm Homeomorph.mulLeft_symm
#align homeomorph.add_left_symm Homeomorph.addLeft_symm

@[to_additive]
lemma isOpenMap_mul_left (a : G) : IsOpenMap (a * ·) := (Homeomorph.mulLeft a).isOpenMap
#align is_open_map_mul_left isOpenMap_mul_left
#align is_open_map_add_left isOpenMap_add_left

@[to_additive IsOpen.left_addCoset]
theorem IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (x • U) :=
  isOpenMap_mul_left x _ h
#align is_open.left_coset IsOpen.leftCoset
#align is_open.left_add_coset IsOpen.left_addCoset

@[to_additive]
lemma isClosedMap_mul_left (a : G) : IsClosedMap (a * ·) := (Homeomorph.mulLeft a).isClosedMap
#align is_closed_map_mul_left isClosedMap_mul_left
#align is_closed_map_add_left isClosedMap_add_left

@[to_additive IsClosed.left_addCoset]
theorem IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (x • U) :=
  isClosedMap_mul_left x _ h
#align is_closed.left_coset IsClosed.leftCoset
#align is_closed.left_add_coset IsClosed.left_addCoset

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with
    continuous_toFun := continuous_id.mul continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.mul_right Homeomorph.mulRight
#align homeomorph.add_right Homeomorph.addRight

@[to_additive (attr := simp)]
lemma Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a) := rfl
#align homeomorph.coe_mul_right Homeomorph.coe_mulRight
#align homeomorph.coe_add_right Homeomorph.coe_addRight

@[to_additive]
theorem Homeomorph.mulRight_symm (a : G) :
    (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl
#align homeomorph.mul_right_symm Homeomorph.mulRight_symm
#align homeomorph.add_right_symm Homeomorph.addRight_symm

@[to_additive]
theorem isOpenMap_mul_right (a : G) : IsOpenMap (· * a) :=
  (Homeomorph.mulRight a).isOpenMap
#align is_open_map_mul_right isOpenMap_mul_right
#align is_open_map_add_right isOpenMap_add_right

@[to_additive IsOpen.right_addCoset]
theorem IsOpen.rightCoset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (op x • U) :=
  isOpenMap_mul_right x _ h
#align is_open.right_coset IsOpen.rightCoset
#align is_open.right_add_coset IsOpen.right_addCoset

@[to_additive]
theorem isClosedMap_mul_right (a : G) : IsClosedMap (· * a) :=
  (Homeomorph.mulRight a).isClosedMap
#align is_closed_map_mul_right isClosedMap_mul_right
#align is_closed_map_add_right isClosedMap_add_right

@[to_additive IsClosed.right_addCoset]
theorem IsClosed.rightCoset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (op x • U) :=
  isClosedMap_mul_right x _ h
#align is_closed.right_coset IsClosed.rightCoset
#align is_closed.right_add_coset IsClosed.right_addCoset

@[to_additive]
theorem discreteTopology_of_isOpen_singleton_one (h : IsOpen ({1} : Set G)) :
    DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  intro g
  suffices {g} = (g⁻¹ * ·) ⁻¹' {1} by
    rw [this]
    exact (continuous_mul_left g⁻¹).isOpen_preimage _ h
  simp only [mul_one, Set.preimage_mul_left_singleton, eq_self_iff_true, inv_inv,
    Set.singleton_eq_singleton_iff]
#align discrete_topology_of_open_singleton_one discreteTopology_of_isOpen_singleton_one
#align discrete_topology_of_open_singleton_zero discreteTopology_of_isOpen_singleton_zero

@[to_additive]
theorem discreteTopology_iff_isOpen_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  ⟨fun h => forall_open_iff_discrete.mpr h {1}, discreteTopology_of_isOpen_singleton_one⟩
#align discrete_topology_iff_open_singleton_one discreteTopology_iff_isOpen_singleton_one
#align discrete_topology_iff_open_singleton_zero discreteTopology_iff_isOpen_singleton_zero

end ContinuousMulGroup

/-!
### `ContinuousInv` and `ContinuousNeg`
-/


/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `AddGroup M` and
`ContinuousAdd M` and `ContinuousNeg M`. -/
class ContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a
#align has_continuous_neg ContinuousNeg
-- Porting note: added
attribute [continuity] ContinuousNeg.continuous_neg

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `Group M` and `ContinuousMul M` and
`ContinuousInv M`. -/
@[to_additive (attr := continuity)]
class ContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹
#align has_continuous_inv ContinuousInv
--#align has_continuous_neg ContinuousNeg
-- Porting note: added
attribute [continuity] ContinuousInv.continuous_inv

export ContinuousInv (continuous_inv)

export ContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [ContinuousInv G]

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
  ⟨continuous_uLift_up.comp (continuous_inv.comp continuous_uLift_down)⟩

@[to_additive]
theorem continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.continuousOn
#align continuous_on_inv continuousOn_inv
#align continuous_on_neg continuousOn_neg

@[to_additive]
theorem continuousWithinAt_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.continuousWithinAt
#align continuous_within_at_inv continuousWithinAt_inv
#align continuous_within_at_neg continuousWithinAt_neg

@[to_additive]
theorem continuousAt_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.continuousAt
#align continuous_at_inv continuousAt_inv
#align continuous_at_neg continuousAt_neg

@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuousAt_inv
#align tendsto_inv tendsto_inv
#align tendsto_neg tendsto_neg

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `Tendsto.inv'`. -/
@[to_additive
  "If a function converges to a value in an additive topological group, then its
  negation converges to the negation of this value."]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.tendsto y).comp h
#align filter.tendsto.inv Filter.Tendsto.inv
#align filter.tendsto.neg Filter.Tendsto.neg

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ :=
  continuous_inv.comp hf
#align continuous.inv Continuous.inv
#align continuous.neg Continuous.neg

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => (f x)⁻¹) x :=
  continuousAt_inv.comp hf
#align continuous_at.inv ContinuousAt.inv
#align continuous_at.neg ContinuousAt.neg

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x)⁻¹) s :=
  continuous_inv.comp_continuousOn hf
#align continuous_on.inv ContinuousOn.inv
#align continuous_on.neg ContinuousOn.neg

@[to_additive]
theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x)⁻¹) s x :=
  Filter.Tendsto.inv hf
#align continuous_within_at.inv ContinuousWithinAt.inv
#align continuous_within_at.neg ContinuousWithinAt.neg

@[to_additive]
instance Prod.continuousInv [TopologicalSpace H] [Inv H] [ContinuousInv H] :
    ContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prod_mk continuous_inv.snd'⟩

variable {ι : Type*}

@[to_additive]
instance Pi.continuousInv {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, ContinuousInv (C i)] : ContinuousInv (∀ i, C i) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.has_continuous_inv Pi.continuousInv
#align pi.has_continuous_neg Pi.continuousNeg

/-- A version of `Pi.continuousInv` for non-dependent functions. It is needed because sometimes
Lean fails to use `Pi.continuousInv` for non-dependent functions. -/
@[to_additive
  "A version of `Pi.continuousNeg` for non-dependent functions. It is needed
  because sometimes Lean fails to use `Pi.continuousNeg` for non-dependent functions."]
instance Pi.has_continuous_inv' : ContinuousInv (ι → G) :=
  Pi.continuousInv
#align pi.has_continuous_inv' Pi.has_continuous_inv'
#align pi.has_continuous_neg' Pi.has_continuous_neg'

@[to_additive]
instance (priority := 100) continuousInv_of_discreteTopology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : ContinuousInv H :=
  ⟨continuous_of_discreteTopology⟩
#align has_continuous_inv_of_discrete_topology continuousInv_of_discreteTopology
#align has_continuous_neg_of_discrete_topology continuousNeg_of_discreteTopology

section PointwiseLimits

variable (G₁ G₂ : Type*) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
theorem isClosed_setOf_map_inv [Inv G₁] [Inv G₂] [ContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply _) (continuous_apply _).inv
#align is_closed_set_of_map_inv isClosed_setOf_map_inv
#align is_closed_set_of_map_neg isClosed_setOf_map_neg

end PointwiseLimits

instance [TopologicalSpace H] [Inv H] [ContinuousInv H] : ContinuousNeg (Additive H) where
  continuous_neg := @continuous_inv H _ _ _

instance [TopologicalSpace H] [Neg H] [ContinuousNeg H] : ContinuousInv (Multiplicative H) where
  continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] {s : Set G}

@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv]
  exact hs.image continuous_inv
#align is_compact.inv IsCompact.inv
#align is_compact.neg IsCompact.neg

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def Homeomorph.inv (G : Type*) [TopologicalSpace G] [InvolutiveInv G]
    [ContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }
#align homeomorph.inv Homeomorph.inv
#align homeomorph.neg Homeomorph.neg

@[to_additive (attr := simp)]
lemma Homeomorph.coe_inv {G : Type*} [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] :
    ⇑(Homeomorph.inv G) = Inv.inv := rfl

@[to_additive]
theorem isOpenMap_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isOpenMap
#align is_open_map_inv isOpenMap_inv
#align is_open_map_neg isOpenMap_neg

@[to_additive]
theorem isClosedMap_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).isClosedMap
#align is_closed_map_inv isClosedMap_inv
#align is_closed_map_neg isClosedMap_neg

variable {G}

@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.preimage continuous_inv
#align is_open.inv IsOpen.inv
#align is_open.neg IsOpen.neg

@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.preimage continuous_inv
#align is_closed.inv IsClosed.inv
#align is_closed.neg IsClosed.neg

@[to_additive]
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure
#align inv_closure inv_closure
#align neg_closure neg_closure

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
#align has_continuous_inv_Inf continuousInv_sInf
#align has_continuous_neg_Inf continuousNeg_sInf

@[to_additive]
theorem continuousInv_iInf {ts' : ι' → TopologicalSpace G}
    (h' : ∀ i, @ContinuousInv G (ts' i) _) : @ContinuousInv G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact continuousInv_sInf (Set.forall_mem_range.mpr h')
#align has_continuous_inv_infi continuousInv_iInf
#align has_continuous_neg_infi continuousNeg_iInf

@[to_additive]
theorem continuousInv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @ContinuousInv G t₁ _)
    (h₂ : @ContinuousInv G t₂ _) : @ContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousInv_iInf fun b => ?_
  cases b <;> assumption
#align has_continuous_inv_inf continuousInv_inf
#align has_continuous_neg_inf continuousNeg_inf

end LatticeOps

@[to_additive]
theorem Inducing.continuousInv {G H : Type*} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [ContinuousInv H] {f : G → H} (hf : Inducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : ContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [(· ∘ ·), hf_inv] using hf.continuous.inv⟩
#align inducing.has_continuous_inv Inducing.continuousInv
#align inducing.has_continuous_neg Inducing.continuousNeg

section TopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `x y ↦ x * y⁻¹` (resp., subtraction) is continuous.
-/

-- Porting note (#11215): TODO should this docstring be extended
-- to match the multiplicative version?
/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class TopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] extends
  ContinuousAdd G, ContinuousNeg G : Prop
#align topological_add_group TopologicalAddGroup

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `UniformSpace` instance,
you should also provide an instance of `UniformSpace` and `UniformGroup` using
`TopologicalGroup.toUniformSpace` and `topologicalCommGroup_isUniform`. -/
-- Porting note: check that these ↑ names exist once they've been ported in the future.
@[to_additive]
class TopologicalGroup (G : Type*) [TopologicalSpace G] [Group G] extends ContinuousMul G,
  ContinuousInv G : Prop
#align topological_group TopologicalGroup
--#align topological_add_group TopologicalAddGroup

section Conj

instance ConjAct.units_continuousConstSMul {M} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] : ContinuousConstSMul (ConjAct Mˣ) M :=
  ⟨fun _ => (continuous_const.mul continuous_id).mul continuous_const⟩
#align conj_act.units_has_continuous_const_smul ConjAct.units_continuousConstSMul

variable [TopologicalSpace G] [Inv G] [Mul G] [ContinuousMul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive
  "Conjugation is jointly continuous on `G × G` when both `add` and `neg` are continuous."]
theorem TopologicalGroup.continuous_conj_prod [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)
#align topological_group.continuous_conj_prod TopologicalGroup.continuous_conj_prod
#align topological_add_group.continuous_conj_sum TopologicalAddGroup.continuous_conj_sum

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive (attr := continuity)
  "Conjugation by a fixed element is continuous when `add` is continuous."]
theorem TopologicalGroup.continuous_conj (g : G) : Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_right g⁻¹).comp (continuous_mul_left g)
#align topological_group.continuous_conj TopologicalGroup.continuous_conj
#align topological_add_group.continuous_conj TopologicalAddGroup.continuous_conj

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive (attr := continuity)
  "Conjugation acting on fixed element of the additive group is continuous when both
    `add` and `neg` are continuous."]
theorem TopologicalGroup.continuous_conj' [ContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_right h).mul continuous_inv
#align topological_group.continuous_conj' TopologicalGroup.continuous_conj'
#align topological_add_group.continuous_conj' TopologicalAddGroup.continuous_conj'

end Conj

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [TopologicalSpace α] {f : α → G}
  {s : Set α} {x : α}

instance : TopologicalGroup (ULift G) where

section ZPow

@[to_additive (attr := continuity)]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | Int.negSucc n => by simpa using (continuous_pow (n + 1)).inv
#align continuous_zpow continuous_zpow
#align continuous_zsmul continuous_zsmul

instance AddGroup.continuousConstSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [TopologicalAddGroup A] : ContinuousConstSMul ℤ A :=
  ⟨continuous_zsmul⟩
#align add_group.has_continuous_const_smul_int AddGroup.continuousConstSMul_int

instance AddGroup.continuousSMul_int {A} [AddGroup A] [TopologicalSpace A]
    [TopologicalAddGroup A] : ContinuousSMul ℤ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_zsmul⟩
#align add_group.has_continuous_smul_int AddGroup.continuousSMul_int

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z :=
  (continuous_zpow z).comp h
#align continuous.zpow Continuous.zpow
#align continuous.zsmul Continuous.zsmul

@[to_additive]
theorem continuousOn_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).continuousOn
#align continuous_on_zpow continuousOn_zpow
#align continuous_on_zsmul continuousOn_zsmul

@[to_additive]
theorem continuousAt_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).continuousAt
#align continuous_at_zpow continuousAt_zpow
#align continuous_at_zsmul continuousAt_zsmul

@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuousAt_zpow _ _).tendsto.comp hf
#align filter.tendsto.zpow Filter.Tendsto.zpow
#align filter.tendsto.zsmul Filter.Tendsto.zsmul

@[to_additive]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (fun x => f x ^ z) s x :=
  Filter.Tendsto.zpow hf z
#align continuous_within_at.zpow ContinuousWithinAt.zpow
#align continuous_within_at.zsmul ContinuousWithinAt.zsmul

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (fun x => f x ^ z) x :=
  Filter.Tendsto.zpow hf z
#align continuous_at.zpow ContinuousAt.zpow
#align continuous_at.zsmul ContinuousAt.zsmul

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (fun x => f x ^ z) s := fun x hx => (hf x hx).zpow z
#align continuous_on.zpow ContinuousOn.zpow
#align continuous_on.zsmul ContinuousOn.zsmul

end ZPow

section OrderedCommGroup

variable [TopologicalSpace H] [OrderedCommGroup H] [ContinuousInv H]

@[to_additive]
theorem tendsto_inv_nhdsWithin_Ioi {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ioi tendsto_inv_nhdsWithin_Ioi
#align tendsto_neg_nhds_within_Ioi tendsto_neg_nhdsWithin_Ioi

@[to_additive]
theorem tendsto_inv_nhdsWithin_Iio {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iio tendsto_inv_nhdsWithin_Iio
#align tendsto_neg_nhds_within_Iio tendsto_neg_nhdsWithin_Iio

@[to_additive]
theorem tendsto_inv_nhdsWithin_Ioi_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Ioi _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ioi_inv tendsto_inv_nhdsWithin_Ioi_inv
#align tendsto_neg_nhds_within_Ioi_neg tendsto_neg_nhdsWithin_Ioi_neg

@[to_additive]
theorem tendsto_inv_nhdsWithin_Iio_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Iio _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iio_inv tendsto_inv_nhdsWithin_Iio_inv
#align tendsto_neg_nhds_within_Iio_neg tendsto_neg_nhdsWithin_Iio_neg

@[to_additive]
theorem tendsto_inv_nhdsWithin_Ici {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ici tendsto_inv_nhdsWithin_Ici
#align tendsto_neg_nhds_within_Ici tendsto_neg_nhdsWithin_Ici

@[to_additive]
theorem tendsto_inv_nhdsWithin_Iic {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iic tendsto_inv_nhdsWithin_Iic
#align tendsto_neg_nhds_within_Iic tendsto_neg_nhdsWithin_Iic

@[to_additive]
theorem tendsto_inv_nhdsWithin_Ici_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Ici _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ici_inv tendsto_inv_nhdsWithin_Ici_inv
#align tendsto_neg_nhds_within_Ici_neg tendsto_neg_nhdsWithin_Ici_neg

@[to_additive]
theorem tendsto_inv_nhdsWithin_Iic_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhdsWithin_Iic _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iic_inv tendsto_inv_nhdsWithin_Iic_inv
#align tendsto_neg_nhds_within_Iic_neg tendsto_neg_nhdsWithin_Iic_neg

end OrderedCommGroup

@[to_additive]
instance [TopologicalSpace H] [Group H] [TopologicalGroup H] : TopologicalGroup (G × H) where
  continuous_inv := continuous_inv.prod_map continuous_inv

@[to_additive]
instance Pi.topologicalGroup {C : β → Type*} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, TopologicalGroup (C b)] : TopologicalGroup (∀ b, C b) where
  continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.topological_group Pi.topologicalGroup
#align pi.topological_add_group Pi.topologicalAddGroup

open MulOpposite

@[to_additive]
instance [Inv α] [ContinuousInv α] : ContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.inducing.continuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [Group α] [TopologicalGroup α] : TopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds inv_one)
#align nhds_one_symm nhds_one_symm
#align nhds_zero_symm nhds_zero_symm

@[to_additive]
theorem nhds_one_symm' : map Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).map_nhds_eq _).trans (congr_arg nhds inv_one)
#align nhds_one_symm' nhds_one_symm'
#align nhds_zero_symm' nhds_zero_symm'

@[to_additive]
theorem inv_mem_nhds_one {S : Set G} (hS : S ∈ (𝓝 1 : Filter G)) : S⁻¹ ∈ 𝓝 (1 : G) := by
  rwa [← nhds_one_symm'] at hS
#align inv_mem_nhds_one inv_mem_nhds_one
#align neg_mem_nhds_zero neg_mem_nhds_zero

/-- The map `(x, y) ↦ (x, x * y)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism. This is a shear mapping."]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    continuous_toFun := continuous_fst.prod_mk continuous_mul
    continuous_invFun := continuous_fst.prod_mk <| continuous_fst.inv.mul continuous_snd }
#align homeomorph.shear_mul_right Homeomorph.shearMulRight
#align homeomorph.shear_add_right Homeomorph.shearAddRight

@[to_additive (attr := simp)]
theorem Homeomorph.shearMulRight_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl
#align homeomorph.shear_mul_right_coe Homeomorph.shearMulRight_coe
#align homeomorph.shear_add_right_coe Homeomorph.shearAddRight_coe

@[to_additive (attr := simp)]
theorem Homeomorph.shearMulRight_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl
#align homeomorph.shear_mul_right_symm_coe Homeomorph.shearMulRight_symm_coe
#align homeomorph.shear_add_right_symm_coe Homeomorph.shearAddRight_symm_coe

variable {G}

@[to_additive]
protected theorem Inducing.topologicalGroup {F : Type*} [Group H] [TopologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : Inducing f) : TopologicalGroup H :=
  { toContinuousMul := hf.continuousMul _
    toContinuousInv := hf.continuousInv (map_inv f) }
#align inducing.topological_group Inducing.topologicalGroup
#align inducing.topological_add_group Inducing.topologicalAddGroup

@[to_additive]
-- Porting note: removed `protected` (needs to be in namespace)
theorem topologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) :
    @TopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.topologicalGroup f ⟨rfl⟩
#align topological_group_induced topologicalGroup_induced
#align topological_add_group_induced topologicalAddGroup_induced

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : TopologicalGroup S :=
  Inducing.topologicalGroup S.subtype inducing_subtype_val

end Subgroup

/-- The (topological-space) closure of a subgroup of a topological group is
itself a subgroup. -/
@[to_additive
  "The (topological-space) closure of an additive subgroup of an additive topological group is
  itself an additive subgroup."]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set G)
    inv_mem' := fun {g} hg => by simpa only [← Set.mem_inv, inv_closure, inv_coe_set] using hg }
#align subgroup.topological_closure Subgroup.topologicalClosure
#align add_subgroup.topological_closure AddSubgroup.topologicalClosure

@[to_additive (attr := simp)]
theorem Subgroup.topologicalClosure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = _root_.closure s :=
  rfl
#align subgroup.topological_closure_coe Subgroup.topologicalClosure_coe
#align add_subgroup.topological_closure_coe AddSubgroup.topologicalClosure_coe

@[to_additive]
theorem Subgroup.le_topologicalClosure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
#align subgroup.le_topological_closure Subgroup.le_topologicalClosure
#align add_subgroup.le_topological_closure AddSubgroup.le_topologicalClosure

@[to_additive]
theorem Subgroup.isClosed_topologicalClosure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := isClosed_closure
#align subgroup.is_closed_topological_closure Subgroup.isClosed_topologicalClosure
#align add_subgroup.is_closed_topological_closure AddSubgroup.isClosed_topologicalClosure

@[to_additive]
theorem Subgroup.topologicalClosure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subgroup.topological_closure_minimal Subgroup.topologicalClosure_minimal
#align add_subgroup.topological_closure_minimal AddSubgroup.topologicalClosure_minimal

@[to_additive]
theorem DenseRange.topologicalClosure_map_subgroup [Group H] [TopologicalSpace H]
    [TopologicalGroup H] {f : G →* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image hf hs
#align dense_range.topological_closure_map_subgroup DenseRange.topologicalClosure_map_subgroup
#align dense_range.topological_closure_map_add_subgroup DenseRange.topologicalClosure_map_addSubgroup

/-- The topological closure of a normal subgroup is normal. -/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
theorem Subgroup.is_normal_topologicalClosure {G : Type*} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] (N : Subgroup G) [N.Normal] : (Subgroup.topologicalClosure N).Normal where
  conj_mem n hn g := by
    apply map_mem_closure (TopologicalGroup.continuous_conj g) hn
    exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g
#align subgroup.is_normal_topological_closure Subgroup.is_normal_topologicalClosure
#align add_subgroup.is_normal_topological_closure AddSubgroup.is_normal_topologicalClosure

@[to_additive]
theorem mul_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) := by
  rw [connectedComponent_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    apply Continuous.image_connectedComponent_subset (continuous_mul_left g)
    rw [← connectedComponent_eq hh]
    exact ⟨(1 : G), mem_connectedComponent, by simp only [mul_one]⟩
  simpa [← connectedComponent_eq hmul] using mem_connectedComponent
#align mul_mem_connected_component_one mul_mem_connectedComponent_one
#align add_mem_connected_component_zero add_mem_connectedComponent_zero

@[to_additive]
theorem inv_mem_connectedComponent_one {G : Type*} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by
  rw [← inv_one]
  exact
    Continuous.image_connectedComponent_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)
#align inv_mem_connected_component_one inv_mem_connectedComponent_one
#align neg_mem_connected_component_zero neg_mem_connectedComponent_zero

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."]
def Subgroup.connectedComponentOfOne (G : Type*) [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' hg hh := mul_mem_connectedComponent_one hg hh
  inv_mem' hg := inv_mem_connectedComponent_one hg
#align subgroup.connected_component_of_one Subgroup.connectedComponentOfOne
#align add_subgroup.connected_component_of_zero AddSubgroup.connectedComponentOfZero

/-- If a subgroup of a topological group is commutative, then so is its topological closure. -/
@[to_additive
  "If a subgroup of an additive topological group is commutative, then so is its
  topological closure."]
def Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subgroup.comm_group_topological_closure Subgroup.commGroupTopologicalClosure
#align add_subgroup.add_comm_group_topological_closure AddSubgroup.addCommGroupTopologicalClosure

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
#align exists_nhds_split_inv exists_nhds_split_inv
#align exists_nhds_half_neg exists_nhds_half_neg

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp
#align nhds_translation_mul_inv nhds_translation_mul_inv
#align nhds_translation_add_neg nhds_translation_add_neg

@[to_additive (attr := simp)]
theorem map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y
#align map_mul_left_nhds map_mul_left_nhds
#align map_add_left_nhds map_add_left_nhds

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x := by simp
#align map_mul_left_nhds_one map_mul_left_nhds_one
#align map_add_left_nhds_zero map_add_left_nhds_zero

@[to_additive (attr := simp)]
theorem map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x) :=
  (Homeomorph.mulRight x).map_nhds_eq y
#align map_mul_right_nhds map_mul_right_nhds
#align map_add_right_nhds map_add_right_nhds

@[to_additive]
theorem map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x := by simp
#align map_mul_right_nhds_one map_mul_right_nhds_one
#align map_add_right_nhds_zero map_add_right_nhds_zero

@[to_additive]
theorem Filter.HasBasis.nhds_of_one {ι : Sort*} {p : ι → Prop} {s : ι → Set G}
    (hb : HasBasis (𝓝 1 : Filter G) p s) (x : G) :
    HasBasis (𝓝 x) p fun i => { y | y / x ∈ s i } := by
  rw [← nhds_translation_mul_inv]
  simp_rw [div_eq_mul_inv]
  exact hb.comap _
#align filter.has_basis.nhds_of_one Filter.HasBasis.nhds_of_one
#align filter.has_basis.nhds_of_zero Filter.HasBasis.nhds_of_zero

@[to_additive]
theorem mem_closure_iff_nhds_one {x : G} {s : Set G} :
    x ∈ closure s ↔ ∀ U ∈ (𝓝 1 : Filter G), ∃ y ∈ s, y / x ∈ U := by
  rw [mem_closure_iff_nhds_basis ((𝓝 1 : Filter G).basis_sets.nhds_of_one x)]
  simp_rw [Set.mem_setOf, id]
#align mem_closure_iff_nhds_one mem_closure_iff_nhds_one
#align mem_closure_iff_nhds_zero mem_closure_iff_nhds_zero

/-- A monoid homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniformContinuous_of_continuousAt_one`. -/
@[to_additive
  "An additive monoid homomorphism (a bundled morphism of a type that implements
  `AddMonoidHomClass`) from an additive topological group to an additive topological monoid is
  continuous provided that it is continuous at zero. See also
  `uniformContinuous_of_continuousAt_zero`."]
theorem continuous_of_continuousAt_one {M hom : Type*} [MulOneClass M] [TopologicalSpace M]
    [ContinuousMul M] [FunLike hom G M] [MonoidHomClass hom G M] (f : hom)
    (hf : ContinuousAt f 1) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, (· ∘ ·), map_mul,
      map_one, mul_one] using hf.tendsto.const_mul (f x)
#align continuous_of_continuous_at_one continuous_of_continuousAt_one
#align continuous_of_continuous_at_zero continuous_of_continuousAt_zero

-- Porting note (#10756): new theorem
@[to_additive continuous_of_continuousAt_zero₂]
theorem continuous_of_continuousAt_one₂ {H M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [Group H] [TopologicalSpace H] [TopologicalGroup H] (f : G →* H →* M)
    (hf : ContinuousAt (fun x : G × H ↦ f x.1 x.2) (1, 1))
    (hl : ∀ x, ContinuousAt (f x) 1) (hr : ∀ y, ContinuousAt (f · y) 1) :
    Continuous (fun x : G × H ↦ f x.1 x.2) := continuous_iff_continuousAt.2 fun (x, y) => by
  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
    prod_map_map_eq, tendsto_map'_iff, (· ∘ ·), map_mul, MonoidHom.mul_apply] at *
  refine ((tendsto_const_nhds.mul ((hr y).comp tendsto_fst)).mul
    (((hl x).comp tendsto_snd).mul hf)).mono_right (le_of_eq ?_)
  simp only [map_one, mul_one, MonoidHom.one_apply]

@[to_additive]
theorem TopologicalGroup.ext {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  TopologicalSpace.ext_nhds fun x ↦ by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]
#align topological_group.ext TopologicalGroup.ext
#align topological_add_group.ext TopologicalAddGroup.ext

@[to_additive]
theorem TopologicalGroup.ext_iff {G : Type*} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩
#align topological_group.ext_iff TopologicalGroup.ext_iff
#align topological_add_group.ext_iff TopologicalAddGroup.ext_iff

@[to_additive]
theorem ContinuousInv.of_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : ContinuousInv G := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have : Tendsto (fun x => x₀⁻¹ * (x₀ * x⁻¹ * x₀⁻¹)) (𝓝 1) (map (x₀⁻¹ * ·) (𝓝 1)) :=
    (tendsto_map.comp <| hconj x₀).comp hinv
  simpa only [ContinuousAt, hleft x₀, hleft x₀⁻¹, tendsto_map'_iff, (· ∘ ·), mul_assoc, mul_inv_rev,
    inv_mul_cancel_left] using this
#align has_continuous_inv.of_nhds_one ContinuousInv.of_nhds_one
#align has_continuous_neg.of_nhds_zero ContinuousNeg.of_nhds_zero

@[to_additive]
theorem TopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : TopologicalGroup G :=
  { toContinuousMul := ContinuousMul.of_nhds_one hmul hleft hright
    toContinuousInv :=
      ContinuousInv.of_nhds_one hinv hleft fun x₀ =>
        le_of_eq
          (by
            rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x * x₀⁻¹) ∘ fun x => x₀ * x from rfl, ←
              map_map, ← hleft, hright, map_map]
            simp [(· ∘ ·)]) }
#align topological_group.of_nhds_one' TopologicalGroup.of_nhds_one'
#align topological_add_group.of_nhds_zero' TopologicalAddGroup.of_nhds_zero'

@[to_additive]
theorem TopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (x₀ * · * x₀⁻¹) (𝓝 1) (𝓝 1)) : TopologicalGroup G := by
  refine TopologicalGroup.of_nhds_one' hmul hinv hleft fun x₀ => ?_
  replace hconj : ∀ x₀ : G, map (x₀ * · * x₀⁻¹) (𝓝 1) = 𝓝 1 :=
    fun x₀ => map_eq_of_inverse (x₀⁻¹ * · * x₀⁻¹⁻¹) (by ext; simp [mul_assoc]) (hconj _) (hconj _)
  rw [← hconj x₀]
  simpa [(· ∘ ·)] using hleft _
#align topological_group.of_nhds_one TopologicalGroup.of_nhds_one
#align topological_add_group.of_nhds_zero TopologicalAddGroup.of_nhds_zero

@[to_additive]
theorem TopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (x₀ * ·) (𝓝 1)) : TopologicalGroup G :=
  TopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)
#align topological_group.of_comm_of_nhds_one TopologicalGroup.of_comm_of_nhds_one
#align topological_add_group.of_comm_of_nhds_zero TopologicalAddGroup.of_comm_of_nhds_zero

end TopologicalGroup

section QuotientTopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] (N : Subgroup G) (n : N.Normal)

@[to_additive]
instance QuotientGroup.Quotient.topologicalSpace {G : Type*} [Group G] [TopologicalSpace G]
    (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuotient
#align quotient_group.quotient.topological_space QuotientGroup.Quotient.topologicalSpace
#align quotient_add_group.quotient.topological_space QuotientAddGroup.Quotient.topologicalSpace

open QuotientGroup

@[to_additive]
theorem QuotientGroup.isOpenMap_coe : IsOpenMap ((↑) : G → G ⧸ N) := by
  intro s s_op
  change IsOpen (((↑) : G → G ⧸ N) ⁻¹' ((↑) '' s))
  rw [QuotientGroup.preimage_image_mk N s]
  exact isOpen_iUnion fun n => (continuous_mul_right _).isOpen_preimage s s_op
#align quotient_group.is_open_map_coe QuotientGroup.isOpenMap_coe
#align quotient_add_group.is_open_map_coe QuotientAddGroup.isOpenMap_coe

@[to_additive]
instance topologicalGroup_quotient [N.Normal] : TopologicalGroup (G ⧸ N) where
  continuous_mul := by
    have cont : Continuous (((↑) : G → G ⧸ N) ∘ fun p : G × G ↦ p.fst * p.snd) :=
      continuous_quot_mk.comp continuous_mul
    have quot : QuotientMap fun p : G × G ↦ ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) := by
      apply IsOpenMap.to_quotientMap
      · exact (QuotientGroup.isOpenMap_coe N).prod (QuotientGroup.isOpenMap_coe N)
      · exact continuous_quot_mk.prod_map continuous_quot_mk
      · exact (surjective_quot_mk _).Prod_map (surjective_quot_mk _)
    exact quot.continuous_iff.2 cont
  continuous_inv := by
    have quot := IsOpenMap.to_quotientMap
      (QuotientGroup.isOpenMap_coe N) continuous_quot_mk (surjective_quot_mk _)
    rw [quot.continuous_iff]
    exact continuous_quot_mk.comp continuous_inv
#align topological_group_quotient topologicalGroup_quotient
#align topological_add_group_quotient topologicalAddGroup_quotient

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
  "Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient."]
theorem QuotientGroup.nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x) :=
  le_antisymm ((QuotientGroup.isOpenMap_coe N).nhds_le x) continuous_quot_mk.continuousAt
#align quotient_group.nhds_eq QuotientGroup.nhds_eq
#align quotient_add_group.nhds_eq QuotientAddGroup.nhds_eq

variable (G)
variable [FirstCountableTopology G]

/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → Set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`QuotientGroup.completeSpace` -/
@[to_additive
  "Any first countable topological additive group has an antitone neighborhood basis
  `u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`.
  The existence of such a neighborhood basis is a key tool for `QuotientAddGroup.completeSpace`"]
theorem TopologicalGroup.exists_antitone_basis_nhds_one :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n := by
  rcases (𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, exists_true_left, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in atTop, u m * u m ⊆ u n := by
    intro n
    rcases this n with ⟨j, k, -, h⟩
    refine atTop_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => ?_⟩
    rintro - ⟨a, ha, b, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := HasAntitoneBasis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩
#align topological_group.exists_antitone_basis_nhds_one TopologicalGroup.exists_antitone_basis_nhds_one
#align topological_add_group.exists_antitone_basis_nhds_zero TopologicalAddGroup.exists_antitone_basis_nhds_zero

/-- In a first countable topological group `G` with normal subgroup `N`, `1 : G ⧸ N` has a
countable neighborhood basis. -/
@[to_additive
  "In a first countable topological additive group `G` with normal additive subgroup
  `N`, `0 : G ⧸ N` has a countable neighborhood basis."]
instance QuotientGroup.nhds_one_isCountablyGenerated : (𝓝 (1 : G ⧸ N)).IsCountablyGenerated :=
  (QuotientGroup.nhds_eq N 1).symm ▸ map.isCountablyGenerated _ _
#align quotient_group.nhds_one_is_countably_generated QuotientGroup.nhds_one_isCountablyGenerated
#align quotient_add_group.nhds_zero_is_countably_generated QuotientAddGroup.nhds_zero_isCountablyGenerated

end QuotientTopologicalGroup

/-- A typeclass saying that `p : G × G ↦ p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class ContinuousSub (G : Type*) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2
#align has_continuous_sub ContinuousSub

/-- A typeclass saying that `p : G × G ↦ p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`. -/
@[to_additive existing]
class ContinuousDiv (G : Type*) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2
#align has_continuous_div ContinuousDiv

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) TopologicalGroup.to_continuousDiv [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : ContinuousDiv G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact continuous_fst.mul continuous_snd.inv⟩
#align topological_group.to_has_continuous_div TopologicalGroup.to_continuousDiv
#align topological_add_group.to_has_continuous_sub TopologicalAddGroup.to_continuousSub

export ContinuousSub (continuous_sub)

export ContinuousDiv (continuous_div')

section ContinuousDiv

variable [TopologicalSpace G] [Div G] [ContinuousDiv G]

@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.div' Filter.Tendsto.div'
#align filter.tendsto.sub Filter.Tendsto.sub

@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h
#align filter.tendsto.const_div' Filter.Tendsto.const_div'
#align filter.tendsto.const_sub Filter.Tendsto.const_sub

@[to_additive]
lemma Filter.tendsto_const_div_iff {G : Type*} [CommGroup G] [TopologicalSpace G] [ContinuousDiv G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (fun k : α ↦ b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, Filter.Tendsto.const_div' b⟩
  convert h.const_div' b with k <;> rw [div_div_cancel]

@[to_additive sub_const]
theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds
#align filter.tendsto.div_const' Filter.Tendsto.div_const'
#align filter.tendsto.sub_const Filter.Tendsto.sub_const

lemma Filter.tendsto_div_const_iff {G : Type*}
    [CommGroupWithZero G] [TopologicalSpace G] [ContinuousDiv G]
    {b : G} (hb : b ≠ 0) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert h.div_const' b⁻¹ with k <;> rw [div_div, mul_inv_cancel hb, div_one]

lemma Filter.tendsto_sub_const_iff {G : Type*}
    [AddCommGroup G] [TopologicalSpace G] [ContinuousSub G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · - b) l (𝓝 (c - b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.sub_const h b⟩
  convert h.sub_const (-b) with k <;> rw [sub_sub, ← sub_eq_add_neg, sub_self, sub_zero]

variable [TopologicalSpace α] {f g : α → G} {s : Set α} {x : α}

@[to_additive (attr := continuity, fun_prop) sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp (hf.prod_mk hg : _)
#align continuous.div' Continuous.div'
#align continuous.sub Continuous.sub

@[to_additive (attr := continuity) continuous_sub_left]
lemma continuous_div_left' (a : G) : Continuous (a / ·) := continuous_const.div' continuous_id
#align continuous_div_left' continuous_div_left'
#align continuous_sub_left continuous_sub_left

@[to_additive (attr := continuity) continuous_sub_right]
lemma continuous_div_right' (a : G) : Continuous (· / a) := continuous_id.div' continuous_const
#align continuous_div_right' continuous_div_right'
#align continuous_sub_right continuous_sub_right

@[to_additive (attr := fun_prop) sub]
theorem ContinuousAt.div' {f g : α → G} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  Filter.Tendsto.div' hf hg
#align continuous_at.div' ContinuousAt.div'
#align continuous_at.sub ContinuousAt.sub

@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  Filter.Tendsto.div' hf hg
#align continuous_within_at.div' ContinuousWithinAt.div'
#align continuous_within_at.sub ContinuousWithinAt.sub

@[to_additive (attr := fun_prop) sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x / g x) s := fun x hx => (hf x hx).div' (hg x hx)
#align continuous_on.div' ContinuousOn.div'
#align continuous_on.sub ContinuousOn.sub

end ContinuousDiv

section DivInvTopologicalGroup

variable [Group G] [TopologicalSpace G] [TopologicalGroup G]

/-- A version of `Homeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! (config := { simpRhs := true }))
  " A version of `Homeomorph.addLeft a (-b)` that is defeq to `a - b`. "]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with
    continuous_toFun := continuous_const.div' continuous_id
    continuous_invFun := continuous_inv.mul continuous_const }
#align homeomorph.div_left Homeomorph.divLeft
#align homeomorph.sub_left Homeomorph.subLeft

@[to_additive]
theorem isOpenMap_div_left (a : G) : IsOpenMap (a / ·) :=
  (Homeomorph.divLeft _).isOpenMap
#align is_open_map_div_left isOpenMap_div_left
#align is_open_map_sub_left isOpenMap_sub_left

@[to_additive]
theorem isClosedMap_div_left (a : G) : IsClosedMap (a / ·) :=
  (Homeomorph.divLeft _).isClosedMap
#align is_closed_map_div_left isClosedMap_div_left
#align is_closed_map_sub_left isClosedMap_sub_left

/-- A version of `Homeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! (config := { simpRhs := true }))
  "A version of `Homeomorph.addRight (-a) b` that is defeq to `b - a`. "]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with
    continuous_toFun := continuous_id.div' continuous_const
    continuous_invFun := continuous_id.mul continuous_const }
#align homeomorph.div_right Homeomorph.divRight
#align homeomorph.sub_right Homeomorph.subRight

@[to_additive]
lemma isOpenMap_div_right (a : G) : IsOpenMap (· / a) := (Homeomorph.divRight a).isOpenMap
#align is_open_map_div_right isOpenMap_div_right
#align is_open_map_sub_right isOpenMap_sub_right

@[to_additive]
lemma isClosedMap_div_right (a : G) : IsClosedMap (· / a) := (Homeomorph.divRight a).isClosedMap
#align is_closed_map_div_right isClosedMap_div_right
#align is_closed_map_sub_right isClosedMap_sub_right

@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩
#align tendsto_div_nhds_one_iff tendsto_div_nhds_one_iff
#align tendsto_sub_nhds_zero_iff tendsto_sub_nhds_zero_iff

@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x
#align nhds_translation_div nhds_translation_div
#align nhds_translation_sub nhds_translation_sub

end DivInvTopologicalGroup

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `Submonoid.top_closure_mul_self_eq` in
`Topology.Algebra.Monoid`.
-/


section ContinuousConstSMul

variable [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousConstSMul α β] {s : Set α}
  {t : Set β}

@[to_additive]
theorem IsOpen.smul_left (ht : IsOpen t) : IsOpen (s • t) := by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _
#align is_open.smul_left IsOpen.smul_left
#align is_open.vadd_left IsOpen.vadd_left

@[to_additive]
theorem subset_interior_smul_right : s • interior t ⊆ interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left
#align subset_interior_smul_right subset_interior_smul_right
#align subset_interior_vadd_right subset_interior_vadd_right

@[to_additive]
theorem smul_mem_nhds (a : α) {x : β} (ht : t ∈ 𝓝 x) : a • t ∈ 𝓝 (a • x) := by
  rcases mem_nhds_iff.1 ht with ⟨u, ut, u_open, hu⟩
  exact mem_nhds_iff.2 ⟨a • u, smul_set_mono ut, u_open.smul a, smul_mem_smul_set hu⟩
#align smul_mem_nhds smul_mem_nhds
#align vadd_mem_nhds vadd_mem_nhds

variable [TopologicalSpace α]

@[to_additive]
theorem subset_interior_smul : interior s • interior t ⊆ interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right
#align subset_interior_smul subset_interior_smul
#align subset_interior_vadd subset_interior_vadd

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace α] [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousInv α]
  [ContinuousSMul α β] {s : Set α} {t : Set β}

@[to_additive]
theorem IsClosed.smul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (s • t) := by
  have : ∀ x ∈ s • t, ∃ g ∈ s, g⁻¹ • x ∈ t := by
    rintro x ⟨g, hgs, y, hyt, rfl⟩
    refine ⟨g, hgs, ?_⟩
    rwa [inv_smul_smul]
  choose! f hf using this
  refine isClosed_of_closure_subset (fun x hx ↦ ?_)
  rcases mem_closure_iff_ultrafilter.mp hx with ⟨u, hust, hux⟩
  have : Ultrafilter.map f u ≤ 𝓟 s :=
    calc Ultrafilter.map f u ≤ map f (𝓟 (s • t)) := map_mono (le_principal_iff.mpr hust)
      _ = 𝓟 (f '' (s • t)) := map_principal
      _ ≤ 𝓟 s := principal_mono.mpr (image_subset_iff.mpr (fun x hx ↦ (hf x hx).1))
  rcases hs.ultrafilter_le_nhds (Ultrafilter.map f u) this with ⟨g, hg, hug⟩
  suffices g⁻¹ • x ∈ t from
    ⟨g, hg, g⁻¹ • x, this, smul_inv_smul _ _⟩
  exact ht.mem_of_tendsto ((Tendsto.inv hug).smul hux)
    (Eventually.mono hust (fun y hy ↦ (hf y hy).2))

/-! One may expect a version of `IsClosed.smul_left_of_isCompact` where `t` is compact and `s` is
closed, but such a lemma can't be true in this level of generality. For a counterexample, consider
`ℚ` acting on `ℝ` by translation, and let `s : Set ℚ := univ`, `t : set ℝ := {0}`. Then `s` is
closed and `t` is compact, but `s +ᵥ t` is the set of all rationals, which is definitely not
closed in `ℝ`.
To fix the proof, we would need to make two additional assumptions:
- for any `x ∈ t`, `s • {x}` is closed
- for any `x ∈ t`, there is a continuous function `g : s • {x} → s` such that, for all
  `y ∈ s • {x}`, we have `y = (g y) • x`
These are fairly specific hypotheses so we don't state this version of the lemmas, but an
interesting fact is that these two assumptions are verified in the case of a `NormedAddTorsor`
(or really, any `AddTorsor` with continuous `-ᵥ`). We prove this special case in
`IsClosed.vadd_right_of_isCompact`. -/

@[to_additive]
theorem MulAction.isClosedMap_quotient [CompactSpace α] :
    letI := orbitRel α β
    IsClosedMap (Quotient.mk' : β → Quotient (orbitRel α β)) := by
  intro t ht
  rw [← quotientMap_quotient_mk'.isClosed_preimage, MulAction.quotient_preimage_image_eq_union_mul]
  convert ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ, ← iUnion_smul_left_image]
  rfl

end ContinuousSMul

section ContinuousConstSMul

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul α α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_left : IsOpen t → IsOpen (s * t) :=
  IsOpen.smul_left
#align is_open.mul_left IsOpen.mul_left
#align is_open.add_left IsOpen.add_left

@[to_additive]
theorem subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
  subset_interior_smul_right
#align subset_interior_mul_right subset_interior_mul_right
#align subset_interior_add_right subset_interior_add_right

@[to_additive]
theorem subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
  subset_interior_smul
#align subset_interior_mul subset_interior_mul
#align subset_interior_add subset_interior_add

@[to_additive]
theorem singleton_mul_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : {a} * s ∈ 𝓝 (a * b) := by
  have := smul_mem_nhds a h
  rwa [← singleton_smul] at this
#align singleton_mul_mem_nhds singleton_mul_mem_nhds
#align singleton_add_mem_nhds singleton_add_mem_nhds

@[to_additive]
theorem singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : {a} * s ∈ 𝓝 a := by
  simpa only [mul_one] using singleton_mul_mem_nhds a h
#align singleton_mul_mem_nhds_of_nhds_one singleton_mul_mem_nhds_of_nhds_one
#align singleton_add_mem_nhds_of_nhds_zero singleton_add_mem_nhds_of_nhds_zero

end ContinuousConstSMul

section ContinuousConstSMulOp

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul αᵐᵒᵖ α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← iUnion_op_smul_set]
  exact isOpen_biUnion fun a _ => hs.smul _
#align is_open.mul_right IsOpen.mul_right
#align is_open.add_right IsOpen.add_right

@[to_additive]
theorem subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right
#align subset_interior_mul_left subset_interior_mul_left
#align subset_interior_add_left subset_interior_add_left

@[to_additive]
theorem subset_interior_mul' : interior s * interior t ⊆ interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left
#align subset_interior_mul' subset_interior_mul'
#align subset_interior_add' subset_interior_add'

@[to_additive]
theorem mul_singleton_mem_nhds (a : α) {b : α} (h : s ∈ 𝓝 b) : s * {a} ∈ 𝓝 (b * a) := by
  simp only [← iUnion_op_smul_set, mem_singleton_iff, iUnion_iUnion_eq_left]
  exact smul_mem_nhds _ h
#align mul_singleton_mem_nhds mul_singleton_mem_nhds
#align add_singleton_mem_nhds add_singleton_mem_nhds

@[to_additive]
theorem mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s ∈ 𝓝 (1 : α)) : s * {a} ∈ 𝓝 a := by
  simpa only [one_mul] using mul_singleton_mem_nhds a h
#align mul_singleton_mem_nhds_of_nhds_one mul_singleton_mem_nhds_of_nhds_one
#align add_singleton_mem_nhds_of_nhds_zero add_singleton_mem_nhds_of_nhds_zero

end ContinuousConstSMulOp

section TopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] {s t : Set G}

@[to_additive]
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht
#align is_open.div_left IsOpen.div_left
#align is_open.sub_left IsOpen.sub_left

@[to_additive]
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs
#align is_open.div_right IsOpen.div_right
#align is_open.sub_right IsOpen.sub_right

@[to_additive]
theorem subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right
#align subset_interior_div_left subset_interior_div_left
#align subset_interior_sub_left subset_interior_sub_left

@[to_additive]
theorem subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left
#align subset_interior_div_right subset_interior_div_right
#align subset_interior_sub_right subset_interior_sub_right

@[to_additive]
theorem subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left
#align subset_interior_div subset_interior_div
#align subset_interior_sub subset_interior_sub

@[to_additive]
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s * closure t = s * t := by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩
#align is_open.mul_closure IsOpen.mul_closure
#align is_open.add_closure IsOpen.add_closure

@[to_additive]
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
    inv_inv]
#align is_open.closure_mul IsOpen.closure_mul
#align is_open.closure_add IsOpen.closure_add

@[to_additive]
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set G) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]
#align is_open.div_closure IsOpen.div_closure
#align is_open.sub_closure IsOpen.sub_closure

@[to_additive]
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set G) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]
#align is_open.closure_div IsOpen.closure_div
#align is_open.closure_sub IsOpen.closure_sub

@[to_additive]
theorem IsClosed.mul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsClosed (s * t) :=
  ht.smul_left_of_isCompact hs

@[to_additive]
theorem IsClosed.mul_right_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (t * s) := by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]
theorem QuotientGroup.isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsClosedMap ((↑) : G → G ⧸ H) := by
  intro t ht
  rw [← quotientMap_quotient_mk'.isClosed_preimage]
  convert ht.mul_right_of_isCompact hH
  refine (QuotientGroup.preimage_image_mk_eq_iUnion_image _ _).trans ?_
  rw [iUnion_subtype, ← iUnion_mul_right_image]
  rfl

@[to_additive]
lemma subset_mul_closure_one (s : Set G) : s ⊆ s * (closure {1} : Set G) := by
  have : s ⊆ s * ({1} : Set G) := by simpa using Subset.rfl
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]
lemma IsCompact.mul_closure_one_eq_closure {K : Set G} (hK : IsCompact K) :
    K * (closure {1} : Set G) = closure K := by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) ⊆ closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ ⊆ closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]
lemma IsClosed.mul_closure_one_eq {F : Set G} (hF : IsClosed F) :
    F * (closure {1} : Set G) = F := by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ ⊆ closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp [hF.closure_eq]

@[to_additive]
lemma compl_mul_closure_one_eq {t : Set G} (ht : t * (closure {1} : Set G) = t) :
    tᶜ * (closure {1} : Set G) = tᶜ := by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x ∈ t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [smul_eq_mul, mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]
lemma compl_mul_closure_one_eq_iff {t : Set G} :
    tᶜ * (closure {1} : Set G) = tᶜ ↔ t * (closure {1} : Set G) = t :=
  ⟨fun h ↦ by simpa using compl_mul_closure_one_eq h, fun h ↦ compl_mul_closure_one_eq h⟩

@[to_additive]
lemma IsOpen.mul_closure_one_eq {U : Set G} (hU : IsOpen U) :
    U * (closure {1} : Set G) = U :=
  compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

end TopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [ContinuousMul G]

@[to_additive]
theorem TopologicalGroup.t1Space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by simpa using isClosedMap_mul_right x _ h⟩
#align topological_group.t1_space TopologicalGroup.t1Space
#align topological_add_group.t1_space TopologicalAddGroup.t1Space

end

section

variable (G) [TopologicalSpace G] [Group G] [TopologicalGroup G]

@[to_additive]
instance (priority := 100) TopologicalGroup.regularSpace : RegularSpace G := by
  refine .of_exists_mem_nhds_isClosed_subset fun a s hs ↦ ?_
  have : Tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff, image_prod] at hUV
  refine ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, ?_⟩
  calc
    closure U ⊆ closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := isOpen_interior.closure_mul U
    _ ⊆ U * V := mul_subset_mul_left interior_subset
    _ ⊆ s := hUV
#align topological_group.regular_space TopologicalGroup.regularSpace
#align topological_add_group.regular_space TopologicalAddGroup.regularSpace

-- `inferInstance` can find these instances now
#align topological_group.t3_space inferInstance
#align topological_add_group.t3_space inferInstance
#align topological_group.t2_space inferInstance
#align topological_add_group.t2_space inferInstance

variable {G}

@[to_additive]
theorem group_inseparable_iff {x y : G} : Inseparable x y ↔ x / y ∈ closure (1 : Set G) := by
  rw [← singleton_one, ← specializes_iff_mem_closure, specializes_comm, specializes_iff_inseparable,
    ← (Homeomorph.mulRight y⁻¹).embedding.inseparable_iff]
  simp [div_eq_mul_inv]
#align group_separation_rel group_inseparable_iff
#align add_group_separation_rel addGroup_inseparable_iff

@[to_additive]
theorem TopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  ⟨fun _ ↦ isClosed_singleton, fun h ↦
    have := TopologicalGroup.t1Space G h; inferInstance⟩
#align topological_group.t2_space_iff_one_closed TopologicalGroup.t2Space_iff_one_closed
#align topological_add_group.t2_space_iff_zero_closed TopologicalAddGroup.t2Space_iff_zero_closed

@[to_additive]
theorem TopologicalGroup.t2Space_of_one_sep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ 𝓝 (1 : G), x ∉ U) :
    T2Space G := by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec ↦ by_contra fun hne ↦ ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
  exact hU <| mem_of_mem_nhds <| hspec.map (continuous_mul_right y⁻¹) (by rwa [mul_inv_self])
#align topological_group.t2_space_of_one_sep TopologicalGroup.t2Space_of_one_sep
#align topological_add_group.t2_space_of_zero_sep TopologicalAddGroup.t2Space_of_zero_sep

/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is closed, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive "Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is closed, symmetric, and satisfies `V + V ⊆ U`."]
theorem exists_closed_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ V ∈ 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W ∩ W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W ∩ W⁻¹ * (W ∩ W⁻¹)
    ⊆ W * W := mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)
  _ ⊆ V * V := mul_subset_mul hW hW
  _ ⊆ U := hV

variable (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

@[to_additive]
instance Subgroup.t3_quotient_of_isClosed (S : Subgroup G) [Subgroup.Normal S]
    [hS : IsClosed (S : Set G)] : T3Space (G ⧸ S) := by
  rw [← QuotientGroup.ker_mk' S] at hS
  haveI := TopologicalGroup.t1Space (G ⧸ S) (quotientMap_quotient_mk'.isClosed_preimage.mp hS)
  infer_instance
#align subgroup.t3_quotient_of_is_closed Subgroup.t3_quotient_of_isClosed
#align add_subgroup.t3_quotient_of_is_closed AddSubgroup.t3_quotient_of_isClosed

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.) -/
@[to_additive
  "A subgroup `S` of an additive topological group `G` acts on `G` properly
  discontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact
  `K`. (See also `DiscreteTopology`."]
theorem Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simp only [image_smul, mem_setOf_eq, coeSubtype, mem_preimage, mem_image, Prod.exists]
      exact Set.smul_inter_ne_empty_iff' }
#align subgroup.properly_discontinuous_smul_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
#align add_subgroup.properly_discontinuous_vadd_of_tendsto_cofinite AddSubgroup.properlyDiscontinuousVAdd_of_tendsto_cofinite

-- attribute [local semireducible] MulOpposite -- Porting note: doesn't work in Lean 4

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`DiscreteTopology`.)

If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousSMul_of_t2Space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
  "A subgroup `S` of an additive topological group `G` acts on `G` properly discontinuously
  on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact `K`.
  (See also `DiscreteTopology`.)

  If `G` is Hausdorff, this can be combined with `t2Space_of_properlyDiscontinuousVAdd_of_t2Space`
  to show that the quotient group `G ⧸ S` is Hausdorff."]
theorem Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.subtype cofinite (cocompact G)) : ProperlyDiscontinuousSMul S.op G :=
  { finite_disjoint_inter_image := by
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prod_map continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      simp only [preimage_compl, compl_compl, coeSubtype, comp_apply] at H
      apply Finite.of_preimage _ (equivOp S).surjective
      convert H using 1
      ext x
      simp only [image_smul, mem_setOf_eq, coeSubtype, mem_preimage, mem_image, Prod.exists]
      exact Set.op_smul_inter_ne_empty_iff }
#align subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite Subgroup.properlyDiscontinuousSMul_opposite_of_tendsto_cofinite
#align add_subgroup.properly_discontinuous_vadd_opposite_of_tendsto_cofinite AddSubgroup.properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [MulOneClass G] [ContinuousMul G]

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
  "Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `K + V ⊆ U`."]
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
      union_subset ((mul_subset_mul_left (V.inter_subset_left W)).trans hV')
        ((mul_subset_mul_left (V.inter_subset_right W)).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩
#align compact_open_separated_mul_right compact_open_separated_mul_right
#align compact_open_separated_add_right compact_open_separated_add_right

open MulOpposite

/-- Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
  "Given a compact set `K` inside an open set `U`, there is an open neighborhood `V` of
  `0` such that `V + K ⊆ U`."]
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (opHomeomorph.isOpenMap U hU)
      (image_subset op hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine ⟨op ⁻¹' V, continuous_op.continuousAt hV, ?_⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'
#align compact_open_separated_mul_left compact_open_separated_mul_left
#align compact_open_separated_add_left compact_open_separated_add_left

end

section

variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
  "A compact set is covered by finitely many left additive translates of a set
    with non-empty interior."]
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (g * ·) ⁻¹' V := by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, interior ((x * ·) ⁻¹' V) := by
    refine
      hK.elim_finite_subcover (fun x => interior <| (x * ·) ⁻¹' V) (fun x => isOpen_interior) ?_
    cases' hV with g₀ hg₀
    refine fun g _ => mem_iUnion.2 ⟨g₀ * g⁻¹, ?_⟩
    refine preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) ?_
    rwa [mem_preimage, Function.id_def, inv_mul_cancel_right]
  exact ⟨t, Subset.trans ht <| iUnion₂_mono fun g _ => interior_subset⟩
#align compact_covered_by_mul_left_translates compact_covered_by_mul_left_translates
#align compact_covered_by_add_left_translates compact_covered_by_add_left_translates

/-- Every weakly locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace
  "Every weakly locally compact separable topological additive group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis."]
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
#align separable_locally_compact_group.sigma_compact_space SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace
#align separable_locally_compact_add_group.sigma_compact_space SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace

/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
  "Given two compact sets in a noncompact additive topological group, there is a
  translate of the second one that is disjoint from the first one."]
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
  simp only [smul_eq_mul, mul_inv_cancel_right]
#align exists_disjoint_smul_of_is_compact exists_disjoint_smul_of_isCompact
#align exists_disjoint_vadd_of_is_compact exists_disjoint_vadd_of_isCompact

/-- A compact neighborhood of `1` in a topological group admits a closed compact subset
that is a neighborhood of `1`. -/
@[to_additive (attr := deprecated IsCompact.isCompact_isClosed_basis_nhds) -- Since 28 Jan 2024
  "A compact neighborhood of `0` in a topological additive group
admits a closed compact subset that is a neighborhood of `0`."]
theorem exists_isCompact_isClosed_subset_isCompact_nhds_one
    {L : Set G} (Lcomp : IsCompact L) (L1 : L ∈ 𝓝 (1 : G)) :
    ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ K ⊆ L ∧ K ∈ 𝓝 (1 : G) :=
  let ⟨K, ⟨hK, hK₁, hK₂⟩, hKL⟩ := (Lcomp.isCompact_isClosed_basis_nhds L1).mem_iff.1 L1
  ⟨K, hK₁, hK₂, hKL, hK⟩

/-- If a point in a topological group has a compact neighborhood, then the group is
locally compact. -/
@[to_additive]
theorem IsCompact.locallyCompactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G}
    (h : K ∈ 𝓝 x) : LocallyCompactSpace G := by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y ↦ ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

/-- A topological group which is weakly locally compact is automatically locally compact. -/
@[to_additive (attr := deprecated WeaklyLocallyCompactSpace.locallyCompactSpace)] -- 28 Jan 2024
theorem instLocallyCompactSpaceOfWeaklyOfGroup [WeaklyLocallyCompactSpace G] :
    LocallyCompactSpace G :=
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- If a function defined on a topological group has a support contained in a
compact set, then either the function is trivial or the group is locally compact. -/
@[to_additive
      "If a function defined on a topological additive group has a support contained in a compact
      set, then either the function is trivial or the group is locally compact."]
theorem eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} {k : Set G} (hk : IsCompact k) (hf : support f ⊆ k) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push_neg at h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := h
  have : k ∈ 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

/-- If a function defined on a topological group has compact support, then either
the function is trivial or the group is locally compact. -/
@[to_additive
      "If a function defined on a topological additive group has compact support,
      then either the function is trivial or the group is locally compact."]
theorem HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G → α} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G :=
  eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

/-- In a locally compact group, any neighborhood of the identity contains a compact closed
neighborhood of the identity, even without separation assumptions on the space. -/
@[to_additive (attr := deprecated isCompact_isClosed_basis_nhds) -- Since 28 Jan 2024
  "In a locally compact additive group, any neighborhood of the identity contains a
  compact closed neighborhood of the identity, even without separation assumptions on the space."]
theorem local_isCompact_isClosed_nhds_of_group [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ K ⊆ U ∧ (1 : G) ∈ interior K :=
  let ⟨K, ⟨hK₁, hKco, hKcl⟩, hKU⟩ := (isCompact_isClosed_basis_nhds (1 : G)).mem_iff.1 hU
  ⟨K, hKco, hKcl, hKU, mem_interior_iff_mem_nhds.2 hK₁⟩
#align local_is_compact_is_closed_nhds_of_group local_isCompact_isClosed_nhds_of_group
#align local_is_compact_is_closed_nhds_of_add_group local_isCompact_isClosed_nhds_of_addGroup

variable (G)

@[to_additive (attr := deprecated exists_mem_nhds_isCompact_isClosed)] -- Since 28 Jan 2024
theorem exists_isCompact_isClosed_nhds_one [WeaklyLocallyCompactSpace G] :
    ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ K ∈ 𝓝 1 :=
  let ⟨K, hK₁, hKcomp, hKcl⟩ := exists_mem_nhds_isCompact_isClosed (1 : G)
  ⟨K, hKcomp, hKcl, hK₁⟩

/-- A quotient of a locally compact group is locally compact. -/
@[to_additive]
instance [LocallyCompactSpace G] (N : Subgroup G) : LocallyCompactSpace (G ⧸ N) := by
  refine ⟨fun x n hn ↦ ?_⟩
  let π := ((↑) : G → G ⧸ N)
  have C : Continuous π := continuous_quotient_mk'
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Quot.exists_rep x
  have : π ⁻¹' n ∈ 𝓝 y := preimage_nhds_coinduced hn
  rcases local_compact_nhds this with ⟨s, s_mem, hs, s_comp⟩
  exact ⟨π '' s, (QuotientGroup.isOpenMap_coe N).image_mem_nhds s_mem, mapsTo'.mp hs,
    s_comp.image C⟩

end

section

variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  calc
    𝓝 (x * y) = map (x * ·) (map (· * y) (𝓝 1 * 𝓝 1)) := by simp
    _ = map₂ (fun a b => x * (a * b * y)) (𝓝 1) (𝓝 1) := by rw [← map₂_mul, map_map₂, map_map₂]
    _ = map₂ (fun a b => x * a * (b * y)) (𝓝 1) (𝓝 1) := by simp only [mul_assoc]
    _ = 𝓝 x * 𝓝 y := by
      rw [← map_mul_left_nhds_one x, ← map_mul_right_nhds_one y, ← map₂_mul, map₂_map_left,
        map₂_map_right]
#align nhds_mul nhds_mul
#align nhds_add nhds_add

/-- On a topological group, `𝓝 : G → Filter G` can be promoted to a `MulHom`. -/
@[to_additive (attr := simps)
  "On an additive topological group, `𝓝 : G → Filter G` can be promoted to an `AddHom`."]
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _
#align nhds_mul_hom nhdsMulHom
#align nhds_add_hom nhdsAddHom

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    TopologicalAddGroup (Additive G) where
  continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [TopologicalAddGroup G] :
    TopologicalGroup (Multiplicative G) where
  continuous_inv := @continuous_neg G _ _ _

section Quotient

variable [Group G] [TopologicalSpace G] [ContinuousMul G] {Γ : Subgroup G}

@[to_additive]
instance QuotientGroup.continuousConstSMul : ContinuousConstSMul G (G ⧸ Γ) where
  continuous_const_smul g := by
     convert ((@continuous_const _ _ _ _ g).mul continuous_id).quotient_map' _
#align quotient_group.has_continuous_const_smul QuotientGroup.continuousConstSMul
#align quotient_add_group.has_continuous_const_vadd QuotientAddGroup.continuousConstVAdd

@[to_additive]
theorem QuotientGroup.continuous_smul₁ (x : G ⧸ Γ) : Continuous fun g : G => g • x := by
  induction x using QuotientGroup.induction_on
  exact continuous_quotient_mk'.comp (continuous_mul_right _)
#align quotient_group.continuous_smul₁ QuotientGroup.continuous_smul₁
#align quotient_add_group.continuous_smul₁ QuotientAddGroup.continuous_smul₁

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
  "The quotient of a second countable additive topological group by a subgroup is second
  countable."]
instance QuotientGroup.secondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ Γ) :=
  ContinuousConstSMul.secondCountableTopology
#align quotient_group.second_countable_topology QuotientGroup.secondCountableTopology
#align quotient_add_group.second_countable_topology QuotientAddGroup.secondCountableTopology

end Quotient

/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive " If `G` is an additive group with topological negation, then it is homeomorphic to
its additive units."]
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩
  continuous_invFun := Units.continuous_val
#align to_units_homeomorph toUnits_homeomorph
#align to_add_units_homeomorph toAddUnits_homeomorph

@[to_additive] theorem Units.embedding_val [Group G] [TopologicalSpace G] [ContinuousInv G] :
    Embedding (val : Gˣ → G) :=
  toUnits_homeomorph.symm.embedding

namespace Units

open MulOpposite (continuous_op continuous_unop)

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
instance [ContinuousMul α] : TopologicalGroup αˣ where
  continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_val⟩

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive
  "The topological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid."]
def Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prod_mk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prod_mk continuous_val.snd',
        continuous_coe_inv.fst'.prod_mk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv
#align units.homeomorph.prod_units Units.Homeomorph.prodUnits
#align add_units.homeomorph.sum_add_units AddUnits.Homeomorph.sumAddUnits

end Units

section LatticeOps

variable {ι : Sort*} [Group G]

@[to_additive]
theorem topologicalGroup_sInf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @TopologicalGroup G t _) : @TopologicalGroup G (sInf ts) _ :=
  letI := sInf ts
  { toContinuousInv :=
      @continuousInv_sInf _ _ _ fun t ht => @TopologicalGroup.toContinuousInv G t _ <| h t ht
    toContinuousMul :=
      @continuousMul_sInf _ _ _ fun t ht =>
        @TopologicalGroup.toContinuousMul G t _ <| h t ht }
#align topological_group_Inf topologicalGroup_sInf
#align topological_add_group_Inf topologicalAddGroup_sInf

@[to_additive]
theorem topologicalGroup_iInf {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @TopologicalGroup G (ts' i) _) : @TopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← sInf_range]
  exact topologicalGroup_sInf (Set.forall_mem_range.mpr h')
#align topological_group_infi topologicalGroup_iInf
#align topological_add_group_infi topologicalAddGroup_iInf

@[to_additive]
theorem topologicalGroup_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @TopologicalGroup G t₁ _)
    (h₂ : @TopologicalGroup G t₂ _) : @TopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine topologicalGroup_iInf fun b => ?_
  cases b <;> assumption
#align topological_group_inf topologicalGroup_inf
#align topological_add_group_inf topologicalAddGroup_inf

end LatticeOps

/-!
### Lattice of group topologies

We define a type class `GroupTopology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → GroupTopology β`.

The additive version `AddGroupTopology α` and corresponding results are provided as well.
-/


/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure GroupTopology (α : Type u) [Group α] extends TopologicalSpace α, TopologicalGroup α :
  Type u
#align group_topology GroupTopology

/-- An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
structure AddGroupTopology (α : Type u) [AddGroup α] extends TopologicalSpace α,
  TopologicalAddGroup α : Type u
#align add_group_topology AddGroupTopology

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_add` suitable for dot notation."]
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  letI := g.toTopologicalSpace
  haveI := g.toTopologicalGroup
  exact continuous_mul
#align group_topology.continuous_mul' GroupTopology.continuous_mul'
#align add_group_topology.continuous_add' AddGroupTopology.continuous_add'

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_neg` suitable for dot notation."]
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous (Inv.inv : α → α) := by
  letI := g.toTopologicalSpace
  haveI := g.toTopologicalGroup
  exact continuous_inv
#align group_topology.continuous_inv' GroupTopology.continuous_inv'
#align add_group_topology.continuous_neg' AddGroupTopology.continuous_neg'

@[to_additive]
theorem toTopologicalSpace_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) :=
  fun f g h => by
    cases f
    cases g
    congr
#align group_topology.to_topological_space_injective GroupTopology.toTopologicalSpace_injective
#align add_group_topology.to_topological_space_injective AddGroupTopology.toTopologicalSpace_injective

@[to_additive (attr := ext)]
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h
#align group_topology.ext' GroupTopology.ext'
#align add_group_topology.ext' AddGroupTopology.ext'

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
  "The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`
  is also open in `t` (`t` is finer than `s`)."]
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]
theorem toTopologicalSpace_le {x y : GroupTopology α} :
    x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl
#align group_topology.to_topological_space_le GroupTopology.toTopologicalSpace_le
#align add_group_topology.to_topological_space_le AddGroupTopology.toTopologicalSpace_le

@[to_additive]
instance : Top (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊤
  ⟨{  continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl
#align group_topology.to_topological_space_top GroupTopology.toTopologicalSpace_top
#align add_group_topology.to_topological_space_top AddGroupTopology.toTopologicalSpace_top

@[to_additive]
instance : Bot (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊥
  ⟨{  continuous_mul := by
        haveI := discreteTopology_bot α
        continuity
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl
#align group_topology.to_topological_space_bot GroupTopology.toTopologicalSpace_bot
#align add_group_topology.to_topological_space_bot AddGroupTopology.toTopologicalSpace_bot

@[to_additive]
instance : BoundedOrder (GroupTopology α) where
  top := ⊤
  le_top x := show x.toTopologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le x := show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
instance : Inf (GroupTopology α) where inf x y := ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl
#align group_topology.to_topological_space_inf GroupTopology.toTopologicalSpace_inf
#align add_group_topology.to_topological_space_inf AddGroupTopology.toTopologicalSpace_inf

@[to_additive]
instance : SemilatticeInf (GroupTopology α) :=
  toTopologicalSpace_injective.semilatticeInf _ toTopologicalSpace_inf

@[to_additive]
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

local notation "cont" => @Continuous _ _

/-- Infimum of a collection of group topologies. -/
@[to_additive "Infimum of a collection of additive group topologies"]
instance : InfSet (GroupTopology α) where
  sInf S :=
    ⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf <| forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]
theorem toTopologicalSpace_sInf (s : Set (GroupTopology α)) :
    (sInf s).toTopologicalSpace = sInf (toTopologicalSpace '' s) := rfl
#align group_topology.to_topological_space_Inf GroupTopology.toTopologicalSpace_sInf
#align add_group_topology.to_topological_space_Inf AddGroupTopology.toTopologicalSpace_sInf

@[to_additive (attr := simp)]
theorem toTopologicalSpace_iInf {ι} (s : ι → GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg sInf (range_comp _ _).symm
#align group_topology.to_topological_space_infi GroupTopology.toTopologicalSpace_iInf
#align add_group_topology.to_topological_space_infi AddGroupTopology.toTopologicalSpace_iInf

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive
  "Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and
  `⊤` the indiscrete topology.

  The infimum of a collection of group topologies is the topology generated by all their open sets
  (which is a group topology).

  The supremum of two group topologies `s` and `t` is the infimum of the family of all group
  topologies contained in the intersection of `s` and `t`."]
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { inferInstanceAs (InfSet (GroupTopology α)),
    inferInstanceAs (PartialOrder (GroupTopology α)) with
    sInf_le := fun S a haS => toTopologicalSpace_le.1 <| sInf_le ⟨a, haS, rfl⟩
    le_sInf := by
      intro S a hab
      apply (inferInstanceAs (CompleteLattice (TopologicalSpace α))).le_sInf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupTopology α) :=
  { inferInstanceAs (BoundedOrder (GroupTopology α)),
    inferInstanceAs (SemilatticeInf (GroupTopology α)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥ }

/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
  "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`
  is the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  sInf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align group_topology.coinduced GroupTopology.coinduced
#align add_group_topology.coinduced AddGroupTopology.coinduced

@[to_additive]
theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f := by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'
#align group_topology.coinduced_continuous GroupTopology.coinduced_continuous
#align add_group_topology.coinduced_continuous AddGroupTopology.coinduced_continuous

end GroupTopology
