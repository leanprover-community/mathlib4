/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.Subgroup.Basic

#align_import group_theory.group_action.basic from "leanprover-community/mathlib"@"d30d31261cdb4d2f5e612eabc3c4bf45556350d5"

/-!
# Basic properties of group actions

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Pointwise

open Function

namespace MulAction

variable (α)

variable [Monoid α] [MulAction α β]

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def orbit (b : β) :=
  Set.range fun x : α => x • b
#align mul_action.orbit MulAction.orbit
#align add_action.orbit AddAction.orbit

variable {α}

@[to_additive]
theorem mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
  Iff.rfl
#align mul_action.mem_orbit_iff MulAction.mem_orbit_iff
#align add_action.mem_orbit_iff AddAction.mem_orbit_iff

@[to_additive (attr := simp)]
theorem mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
  ⟨x, rfl⟩
#align mul_action.mem_orbit MulAction.mem_orbit
#align add_action.mem_orbit AddAction.mem_orbit

@[to_additive (attr := simp)]
theorem mem_orbit_self (b : β) : b ∈ orbit α b :=
  ⟨1, by simp [MulAction.one_smul]⟩
#align mul_action.mem_orbit_self MulAction.mem_orbit_self
#align add_action.mem_orbit_self AddAction.mem_orbit_self

@[to_additive]
theorem orbit_nonempty (b : β) : Set.Nonempty (orbit α b) :=
  Set.range_nonempty _
#align mul_action.orbit_nonempty MulAction.orbit_nonempty
#align add_action.orbit_nonempty AddAction.orbit_nonempty

@[to_additive]
theorem mapsTo_smul_orbit (a : α) (b : β) : Set.MapsTo ((· • ·) a) (orbit α b) (orbit α b) :=
  Set.range_subset_iff.2 fun a' => ⟨a * a', mul_smul _ _ _⟩
#align mul_action.maps_to_smul_orbit MulAction.mapsTo_smul_orbit
#align add_action.maps_to_vadd_orbit AddAction.mapsTo_vadd_orbit

@[to_additive]
theorem smul_orbit_subset (a : α) (b : β) : a • orbit α b ⊆ orbit α b :=
  (mapsTo_smul_orbit a b).image_subset
#align mul_action.smul_orbit_subset MulAction.smul_orbit_subset
#align add_action.vadd_orbit_subset AddAction.vadd_orbit_subset

@[to_additive]
theorem orbit_smul_subset (a : α) (b : β) : orbit α (a • b) ⊆ orbit α b :=
  Set.range_subset_iff.2 fun a' => mul_smul a' a b ▸ mem_orbit _ _
#align mul_action.orbit_smul_subset MulAction.orbit_smul_subset
#align add_action.orbit_vadd_subset AddAction.orbit_vadd_subset

@[to_additive]
instance {b : β} : MulAction α (orbit α b) where
  smul a := (mapsTo_smul_orbit a b).restrict _ _ _
  one_smul a := Subtype.ext (one_smul α (a : β))
  mul_smul a a' b' := Subtype.ext (mul_smul a a' (b' : β))

@[to_additive (attr := simp)]
theorem orbit.coe_smul {b : β} {a : α} {b' : orbit α b} : ↑(a • b') = a • (b' : β) :=
  rfl
#align mul_action.orbit.coe_smul MulAction.orbit.coe_smul
#align add_action.orbit.coe_vadd AddAction.orbit.coe_vadd

variable (α) (β)

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def fixedPoints : Set β :=
  { b : β | ∀ x : α, x • b = b }
#align mul_action.fixed_points MulAction.fixedPoints
#align add_action.fixed_points AddAction.fixedPoints

/-- `fixedBy g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixedBy g` is the subfield of elements fixed by `g`."]
def fixedBy (g : α) : Set β :=
  { x | g • x = x }
#align mul_action.fixed_by MulAction.fixedBy
#align add_action.fixed_by AddAction.fixedBy

@[to_additive]
theorem fixed_eq_iInter_fixedBy : fixedPoints α β = ⋂ g : α, fixedBy α β g :=
  Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun g => hx g, fun hx g => (Set.mem_iInter.1 hx g : _)⟩
#align mul_action.fixed_eq_Inter_fixed_by MulAction.fixed_eq_iInter_fixedBy
#align add_action.fixed_eq_Inter_fixed_by AddAction.fixed_eq_iInter_fixedBy

variable {α}

@[to_additive (attr := simp)]
theorem mem_fixedPoints {b : β} : b ∈ fixedPoints α β ↔ ∀ x : α, x • b = b :=
  Iff.rfl
#align mul_action.mem_fixed_points MulAction.mem_fixedPoints
#align add_action.mem_fixed_points AddAction.mem_fixedPoints

@[to_additive (attr := simp)]
theorem mem_fixedBy {g : α} {b : β} : b ∈ fixedBy α β g ↔ g • b = b :=
  Iff.rfl
#align mul_action.mem_fixed_by MulAction.mem_fixedBy
#align add_action.mem_fixed_by AddAction.mem_fixedBy

@[to_additive]
theorem mem_fixedPoints' {b : β} : b ∈ fixedPoints α β ↔ ∀ b', b' ∈ orbit α b → b' = b :=
  ⟨fun h _ h₁ =>
    let ⟨x, hx⟩ := mem_orbit_iff.1 h₁
    hx ▸ h x,
    fun h _ => h _ (mem_orbit _ _)⟩
#align mul_action.mem_fixed_points' MulAction.mem_fixedPoints'
#align add_action.mem_fixed_points' AddAction.mem_fixedPoints'

variable (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def Stabilizer.submonoid (b : β) : Submonoid α where
  carrier := { a | a • b = b }
  one_mem' := one_smul _ b
  mul_mem' {a a'} (ha : a • b = b) (hb : a' • b = b) :=
    show (a * a') • b = b by rw [← smul_smul, hb, ha]
#align mul_action.stabilizer.submonoid MulAction.Stabilizer.submonoid
#align add_action.stabilizer.add_submonoid AddAction.Stabilizer.addSubmonoid

@[to_additive (attr := simp)]
theorem mem_stabilizer_submonoid_iff {b : β} {a : α} : a ∈ Stabilizer.submonoid α b ↔ a • b = b :=
  Iff.rfl
#align mul_action.mem_stabilizer_submonoid_iff MulAction.mem_stabilizer_submonoid_iff
#align add_action.mem_stabilizer_add_submonoid_iff AddAction.mem_stabilizer_addSubmonoid_iff

@[to_additive]
theorem orbit_eq_univ [IsPretransitive α β] (x : β) : orbit α x = Set.univ :=
  (surjective_smul α x).range_eq
#align mul_action.orbit_eq_univ MulAction.orbit_eq_univ
#align add_action.orbit_eq_univ AddAction.orbit_eq_univ

variable {α}

@[to_additive]
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : β} [Fintype (orbit α a)] :
    a ∈ fixedPoints α β ↔ Fintype.card (orbit α a) = 1 := by
  rw [Fintype.card_eq_one_iff, mem_fixedPoints]
  constructor
  · exact fun h => ⟨⟨a, mem_orbit_self _⟩, fun ⟨b, ⟨x, hx⟩⟩ => Subtype.eq <| by simp [h x, hx.symm]⟩
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc
      x • a = z := Subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      _ = a := (Subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm
#align mul_action.mem_fixed_points_iff_card_orbit_eq_one MulAction.mem_fixedPoints_iff_card_orbit_eq_one
#align add_action.mem_fixed_points_iff_card_orbit_eq_zero AddAction.mem_fixedPoints_iff_card_orbit_eq_zero

end MulAction

namespace MulAction

variable (α)

variable [Group α] [MulAction α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.
      An additive subgroup."]
def stabilizer (b : β) : Subgroup α :=
  { Stabilizer.submonoid α b with
    inv_mem' := fun {a} (ha : a • b = b) => show a⁻¹ • b = b by rw [inv_smul_eq_iff, ha] }
#align mul_action.stabilizer MulAction.stabilizer
#align add_action.stabilizer AddAction.stabilizer

variable {α}

@[to_additive (attr := simp)]
theorem mem_stabilizer_iff {b : β} {a : α} : a ∈ stabilizer α b ↔ a • b = b :=
  Iff.rfl
#align mul_action.mem_stabilizer_iff MulAction.mem_stabilizer_iff
#align add_action.mem_stabilizer_iff AddAction.mem_stabilizer_iff

@[to_additive (attr := simp)]
theorem smul_orbit (a : α) (b : β) : a • orbit α b = orbit α b :=
  (smul_orbit_subset a b).antisymm <|
    calc
      orbit α b = a • a⁻¹ • orbit α b := (smul_inv_smul _ _).symm
      _ ⊆ a • orbit α b := Set.image_subset _ (smul_orbit_subset _ _)
#align mul_action.smul_orbit MulAction.smul_orbit
#align add_action.vadd_orbit AddAction.vadd_orbit

@[to_additive (attr := simp)]
theorem orbit_smul (a : α) (b : β) : orbit α (a • b) = orbit α b :=
  (orbit_smul_subset a b).antisymm <|
    calc
      orbit α b = orbit α (a⁻¹ • a • b) := by rw [inv_smul_smul]
      _ ⊆ orbit α (a • b) := orbit_smul_subset _ _
#align mul_action.orbit_smul MulAction.orbit_smul
#align add_action.orbit_vadd AddAction.orbit_vadd

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (x : β) : IsPretransitive α (orbit α x) :=
  ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    use b * a⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
theorem orbit_eq_iff {a b : β} : orbit α a = orbit α b ↔ a ∈ orbit α b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩
#align mul_action.orbit_eq_iff MulAction.orbit_eq_iff
#align add_action.orbit_eq_iff AddAction.orbit_eq_iff

variable (α)

@[to_additive]
theorem mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) := by
  simp only [orbit_smul, mem_orbit_self]
#align mul_action.mem_orbit_smul MulAction.mem_orbit_smul
#align add_action.mem_orbit_vadd AddAction.mem_orbit_vadd

@[to_additive]
theorem smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) := by
  simp only [orbit_smul, mem_orbit]
#align mul_action.smul_mem_orbit_smul MulAction.smul_mem_orbit_smul
#align add_action.vadd_mem_orbit_vadd AddAction.vadd_mem_orbit_vadd

variable (β)

/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbitRel : Setoid β where
  r a b := a ∈ orbit α b
  iseqv :=
    ⟨mem_orbit_self, fun {a b} => by simp [orbit_eq_iff.symm, eq_comm], fun {a b} => by
      simp (config := { contextual := true }) [orbit_eq_iff.symm, eq_comm]⟩
#align mul_action.orbit_rel MulAction.orbitRel
#align add_action.orbit_rel AddAction.orbitRel

variable {α} {β}

@[to_additive]
theorem orbitRel_apply {x y : β} : (orbitRel α β).Rel x y ↔ x ∈ orbit α y :=
  Iff.rfl
#align mul_action.orbit_rel_apply MulAction.orbitRel_apply
#align add_action.orbit_rel_apply AddAction.orbitRel_apply

/-- When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `α`. -/
@[to_additive
      "When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the
      union of the orbit of `U` under `α`."]
theorem quotient_preimage_image_eq_union_mul (U : Set β) :
    letI := orbitRel α β
    Quotient.mk' ⁻¹' (Quotient.mk' '' U) = ⋃ a : α, (· • ·) a '' U := by
  letI := orbitRel α β
  set f : β → Quotient (MulAction.orbitRel α β) := Quotient.mk'
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨a, rfl⟩ := Quotient.exact hxy
    rw [Set.mem_iUnion]
    exact ⟨a⁻¹, a • x, hy, inv_smul_smul a x⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨a, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image_iff_bex]
    refine' ⟨a⁻¹ • x, _, by simp only [Quotient.eq']; use a⁻¹⟩
    rw [← hu₂]
    convert hu₁
    simp only [inv_smul_smul]
#align mul_action.quotient_preimage_image_eq_union_mul MulAction.quotient_preimage_image_eq_union_mul
#align add_action.quotient_preimage_image_eq_union_add AddAction.quotient_preimage_image_eq_union_add

@[to_additive]
theorem disjoint_image_image_iff {U V : Set β} :
    letI := orbitRel α β
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V := by
  letI := orbitRel α β
  set f : β → Quotient (MulAction.orbitRel α β) := Quotient.mk'
  refine'
    ⟨fun h x x_in_U a a_in_V =>
      h.le_bot ⟨⟨x, x_in_U, Quotient.sound ⟨a⁻¹, _⟩⟩, ⟨a • x, a_in_V, rfl⟩⟩, _⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro x ⟨y, hy₁, hy₂⟩ ⟨z, hz₁, hz₂⟩
    obtain ⟨a, rfl⟩ := Quotient.exact (hz₂.trans hy₂.symm)
    exact h y hy₁ a hz₁
#align mul_action.disjoint_image_image_iff MulAction.disjoint_image_image_iff
#align add_action.disjoint_image_image_iff AddAction.disjoint_image_image_iff

@[to_additive]
theorem image_inter_image_iff (U V : Set β) :
    letI := orbitRel α β
    Quotient.mk' '' U ∩ Quotient.mk' '' V = ∅ ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff
#align mul_action.image_inter_image_iff MulAction.image_inter_image_iff
#align add_action.image_inter_image_iff AddAction.image_inter_image_iff

variable (α β)

/-- The quotient by `MulAction.orbitRel`, given a name to enable dot notation. -/
@[to_additive (attr := reducible)
    "The quotient by `AddAction.orbitRel`, given a name to enable dot notation."]
def orbitRel.Quotient : Type _ :=
  _root_.Quotient <| orbitRel α β
#align mul_action.orbit_rel.quotient MulAction.orbitRel.Quotient
#align add_action.orbit_rel.quotient AddAction.orbitRel.Quotient

variable {α β}

/-- The orbit corresponding to an element of the quotient by `MulAction.orbitRel` -/
@[to_additive "The orbit corresponding to an element of the quotient by `add_action.orbit_rel`"]
nonrec def orbitRel.Quotient.orbit (x : orbitRel.Quotient α β) : Set β :=
  Quotient.liftOn' x (orbit α) fun _ _ => MulAction.orbit_eq_iff.2
#align mul_action.orbit_rel.quotient.orbit MulAction.orbitRel.Quotient.orbit
#align add_action.orbit_rel.quotient.orbit AddAction.orbitRel.Quotient.orbit

@[to_additive (attr := simp)]
theorem orbitRel.Quotient.orbit_mk (b : β) :
    orbitRel.Quotient.orbit (Quotient.mk'' b : orbitRel.Quotient α β) = MulAction.orbit α b :=
  rfl
#align mul_action.orbit_rel.quotient.orbit_mk MulAction.orbitRel.Quotient.orbit_mk
#align add_action.orbit_rel.quotient.orbit_mk AddAction.orbitRel.Quotient.orbit_mk

@[to_additive]
theorem orbitRel.Quotient.mem_orbit {b : β} {x : orbitRel.Quotient α β} :
    b ∈ x.orbit ↔ Quotient.mk'' b = x := by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl
#align mul_action.orbit_rel.quotient.mem_orbit MulAction.orbitRel.Quotient.mem_orbit
#align add_action.orbit_rel.quotient.mem_orbit AddAction.orbitRel.Quotient.mem_orbit

/-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/
@[to_additive "Note that `hφ = quotient.out_eq'` is a useful choice here."]
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient α β)
    {φ : orbitRel.Quotient α β → β} (hφ : letI := orbitRel α β; RightInverse φ Quotient.mk') :
    orbitRel.Quotient.orbit x = MulAction.orbit α (φ x) := by
  conv_lhs => rw [← hφ x]
#align mul_action.orbit_rel.quotient.orbit_eq_orbit_out MulAction.orbitRel.Quotient.orbit_eq_orbit_out
#align add_action.orbit_rel.quotient.orbit_eq_orbit_out AddAction.orbitRel.Quotient.orbit_eq_orbit_out

variable (α) (β)

-- mathport name: exprΩ
local notation "Ω" => orbitRel.Quotient α β

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `MulAction.orbitRel.Quotient.orbit` instead of
`MulAction.orbit`, to avoid mentioning `Quotient.out'`. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group action.

      This version is expressed in terms of `AddAction.orbitRel.Quotient.orbit` instead of
      `AddAction.orbit`, to avoid mentioning `Quotient.out'`. "]
def selfEquivSigmaOrbits' : β ≃ Σω : Ω, ω.orbit :=
  letI := orbitRel α β
  calc
    β ≃ Σω : Ω, { b // Quotient.mk' b = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm
#align mul_action.self_equiv_sigma_orbits' MulAction.selfEquivSigmaOrbits'
#align add_action.self_equiv_sigma_orbits' AddAction.selfEquivSigmaOrbits'

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
      action."]
def selfEquivSigmaOrbits : β ≃ Σω : Ω, orbit α ω.out' :=
  (selfEquivSigmaOrbits' α β).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits MulAction.selfEquivSigmaOrbits
#align add_action.self_equiv_sigma_orbits AddAction.selfEquivSigmaOrbits

variable {α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g • x) = (stabilizer α x).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_inv,
    one_smul, ← mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
#align mul_action.stabilizer_smul_eq_stabilizer_map_conj MulAction.stabilizer_smul_eq_stabilizer_map_conj

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃* stabilizer α y :=
  let g : α := Classical.choose h
  have hg : g • y = x := Classical.choose_spec h
  have this : stabilizer α x = (stabilizer α y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer α y).symm
#align mul_action.stabilizer_equiv_stabilizer_of_orbit_rel MulAction.stabilizerEquivStabilizerOfOrbitRel

end MulAction

namespace AddAction

variable [AddGroup α] [AddAction α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g +ᵥ x) = (stabilizer α x).map (AddAut.conj g).toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd,
    add_left_neg, zero_vadd, ← mem_stabilizer_iff, AddSubgroup.mem_map_equiv,
    AddAut.conj_symm_apply]
#align add_action.stabilizer_vadd_eq_stabilizer_map_conj AddAction.stabilizer_vadd_eq_stabilizer_map_conj

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃+ stabilizer α y :=
  let g : α := Classical.choose h
  have hg : g +ᵥ y = x := Classical.choose_spec h
  have this : stabilizer α x = (stabilizer α y).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer α y).symm
#align add_action.stabilizer_equiv_stabilizer_of_orbit_rel AddAction.stabilizerEquivStabilizerOfOrbitRel

end AddAction

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `NoZeroSMulDivisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type _} [Monoid M] [NonUnitalNonAssocRing R]
    [DistribMulAction M R] (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine' h _ _
  rw [smul_sub, h', sub_self]
#align smul_cancel_of_non_zero_divisor smul_cancel_of_non_zero_divisor
