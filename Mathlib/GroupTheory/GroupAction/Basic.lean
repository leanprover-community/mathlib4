/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Group

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


universe u v

open Pointwise

open Function

namespace MulAction

variable (M : Type u) [Monoid M] (α : Type v) [MulAction M α]

section Orbit

variable {α}

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def orbit (a : α) :=
  Set.range fun m : M => m • a
#align mul_action.orbit MulAction.orbit
#align add_action.orbit AddAction.orbit

variable {M}

@[to_additive]
theorem mem_orbit_iff {a₁ a₂ : α} : a₂ ∈ orbit M a₁ ↔ ∃ x : M, x • a₁ = a₂ :=
  Iff.rfl
#align mul_action.mem_orbit_iff MulAction.mem_orbit_iff
#align add_action.mem_orbit_iff AddAction.mem_orbit_iff

@[to_additive (attr := simp)]
theorem mem_orbit (a : α) (m : M) : m • a ∈ orbit M a :=
  ⟨m, rfl⟩
#align mul_action.mem_orbit MulAction.mem_orbit
#align add_action.mem_orbit AddAction.mem_orbit

@[to_additive (attr := simp)]
theorem mem_orbit_self (a : α) : a ∈ orbit M a :=
  ⟨1, by simp [MulAction.one_smul]⟩
#align mul_action.mem_orbit_self MulAction.mem_orbit_self
#align add_action.mem_orbit_self AddAction.mem_orbit_self

@[to_additive]
theorem orbit_nonempty (a : α) : Set.Nonempty (orbit M a) :=
  Set.range_nonempty _
#align mul_action.orbit_nonempty MulAction.orbit_nonempty
#align add_action.orbit_nonempty AddAction.orbit_nonempty

@[to_additive]
theorem mapsTo_smul_orbit (m : M) (a : α) : Set.MapsTo (m • ·) (orbit M a) (orbit M a) :=
  Set.range_subset_iff.2 fun m' => ⟨m * m', mul_smul _ _ _⟩
#align mul_action.maps_to_smul_orbit MulAction.mapsTo_smul_orbit
#align add_action.maps_to_vadd_orbit AddAction.mapsTo_vadd_orbit

@[to_additive]
theorem smul_orbit_subset (m : M) (a : α) : m • orbit M a ⊆ orbit M a :=
  (mapsTo_smul_orbit m a).image_subset
#align mul_action.smul_orbit_subset MulAction.smul_orbit_subset
#align add_action.vadd_orbit_subset AddAction.vadd_orbit_subset

@[to_additive]
theorem orbit_smul_subset (m : M) (a : α) : orbit M (m • a) ⊆ orbit M a :=
  Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _
#align mul_action.orbit_smul_subset MulAction.orbit_smul_subset
#align add_action.orbit_vadd_subset AddAction.orbit_vadd_subset

@[to_additive]
instance {a : α} : MulAction M (orbit M a) where
  smul m := (mapsTo_smul_orbit m a).restrict _ _ _
  one_smul m := Subtype.ext (one_smul M (m : α))
  mul_smul m m' a' := Subtype.ext (mul_smul m m' (a' : α))

@[to_additive (attr := simp)]
theorem orbit.coe_smul {a : α} {m : M} {a' : orbit M a} : ↑(m • a') = m • (a' : α) :=
  rfl
#align mul_action.orbit.coe_smul MulAction.orbit.coe_smul
#align add_action.orbit.coe_vadd AddAction.orbit.coe_vadd

@[to_additive]
lemma orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a ⊆ orbit M a := by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
lemma mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a ∈ orbit S b) :
    a ∈ orbit M b :=
  orbit_submonoid_subset S _ h

variable (M)

@[to_additive]
theorem orbit_eq_univ [IsPretransitive M α] (a : α) : orbit M a = Set.univ :=
  (surjective_smul M a).range_eq
#align mul_action.orbit_eq_univ MulAction.orbit_eq_univ
#align add_action.orbit_eq_univ AddAction.orbit_eq_univ

end Orbit

section FixedPoints

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def fixedPoints : Set α :=
  { a : α | ∀ m : M, m • a = a }
#align mul_action.fixed_points MulAction.fixedPoints
#align add_action.fixed_points AddAction.fixedPoints

variable {M}

/-- `fixedBy m` is the set of elements fixed by `m`. -/
@[to_additive "`fixedBy m` is the set of elements fixed by `m`."]
def fixedBy (m : M) : Set α :=
  { x | m • x = x }
#align mul_action.fixed_by MulAction.fixedBy
#align add_action.fixed_by AddAction.fixedBy

variable (M)

@[to_additive]
theorem fixed_eq_iInter_fixedBy : fixedPoints M α = ⋂ m : M, fixedBy α m :=
  Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m : _)⟩
#align mul_action.fixed_eq_Inter_fixed_by MulAction.fixed_eq_iInter_fixedBy
#align add_action.fixed_eq_Inter_fixed_by AddAction.fixed_eq_iInter_fixedBy

variable {M α}

@[to_additive (attr := simp)]
theorem mem_fixedPoints {a : α} : a ∈ fixedPoints M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl
#align mul_action.mem_fixed_points MulAction.mem_fixedPoints
#align add_action.mem_fixed_points AddAction.mem_fixedPoints

@[to_additive (attr := simp)]
theorem mem_fixedBy {m : M} {a : α} : a ∈ fixedBy α m ↔ m • a = a :=
  Iff.rfl
#align mul_action.mem_fixed_by MulAction.mem_fixedBy
#align add_action.mem_fixed_by AddAction.mem_fixedBy

@[to_additive]
theorem mem_fixedPoints' {a : α} : a ∈ fixedPoints M α ↔ ∀ a', a' ∈ orbit M a → a' = a :=
  ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩
#align mul_action.mem_fixed_points' MulAction.mem_fixedPoints'
#align add_action.mem_fixed_points' AddAction.mem_fixedPoints'

@[to_additive mem_fixedPoints_iff_card_orbit_eq_one]
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : α} [Fintype (orbit M a)] :
    a ∈ fixedPoints M α ↔ Fintype.card (orbit M a) = 1 := by
  rw [Fintype.card_eq_one_iff, mem_fixedPoints]
  constructor
  · exact fun h => ⟨⟨a, mem_orbit_self _⟩, fun ⟨a, ⟨x, hx⟩⟩ => Subtype.eq <| by simp [h x, hx.symm]⟩
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc
      x • a = z := Subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      _ = a := (Subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm
#align mul_action.mem_fixed_points_iff_card_orbit_eq_one MulAction.mem_fixedPoints_iff_card_orbit_eq_one
#align add_action.mem_fixed_points_iff_card_orbit_eq_zero AddAction.mem_fixedPoints_iff_card_orbit_eq_one

end FixedPoints

section Stabilizers

variable {α}

/-- The stabilizer of a point `a` as a submonoid of `M`. -/
@[to_additive "The stabilizer of a point `a` as an additive submonoid of `M`."]
def stabilizerSubmonoid (a : α) : Submonoid M where
  carrier := { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]
#align mul_action.stabilizer.submonoid MulAction.stabilizerSubmonoid
#align add_action.stabilizer.add_submonoid AddAction.stabilizerAddSubmonoid

variable {M}

@[to_additive]
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizerSubmonoid M a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
theorem mem_stabilizerSubmonoid_iff {a : α} {m : M} : m ∈ stabilizerSubmonoid M a ↔ m • a = a :=
  Iff.rfl
#align mul_action.mem_stabilizer_submonoid_iff MulAction.mem_stabilizerSubmonoid_iff
#align add_action.mem_stabilizer_add_submonoid_iff AddAction.mem_stabilizerAddSubmonoid_iff

end Stabilizers

end MulAction

section FixedPoints

variable (M : Type u) (α : Type v) [Monoid M]

section Monoid

variable [Monoid α] [MulDistribMulAction M α]

/-- The submonoid of elements fixed under the whole action. -/
def FixedPoints.submonoid : Submonoid α where
  carrier := MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]
lemma FixedPoints.mem_submonoid (a : α) : a ∈ submonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end Monoid

section Group

variable [Group α] [MulDistribMulAction M α]

/-- The subgroup of elements fixed under the whole action. -/
def FixedPoints.subgroup : Subgroup α where
  __ := submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

/-- The notation for `FixedPoints.subgroup`, chosen to resemble `αᴹ`. -/
notation α "^*" M:51 => FixedPoints.subgroup M α

@[simp]
lemma FixedPoints.mem_subgroup (a : α) : a ∈ α^*M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma FixedPoints.subgroup_toSubmonoid : (α^*M).toSubmonoid = submonoid M α :=
  rfl

end Group

section AddMonoid

variable [AddMonoid α] [DistribMulAction M α]

/-- The additive submonoid of elements fixed under the whole action. -/
def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
lemma FixedPoints.mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end AddMonoid

section AddGroup

variable [AddGroup α] [DistribMulAction M α]

/-- The additive subgroup of elements fixed under the whole action. -/
def FixedPoints.addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

/-- The notation for `FixedPoints.addSubgroup`, chosen to resemble `αᴹ`. -/
notation α "^+" M:51 => FixedPoints.addSubgroup M α

@[simp]
lemma FixedPoints.mem_addSubgroup (a : α) : a ∈ α^+M ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
lemma FixedPoints.addSubgroup_toAddSubmonoid : (α^+M).toAddSubmonoid = addSubmonoid M α :=
  rfl

end AddGroup

end FixedPoints

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `IsSMulRegular`.
The typeclass that restricts all terms of `M` to have this property is `NoZeroSMulDivisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type*} [Monoid M] [NonUnitalNonAssocRing R]
    [DistribMulAction M R] (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine h _ ?_
  rw [smul_sub, h', sub_self]
#align smul_cancel_of_non_zero_divisor smul_cancel_of_non_zero_divisor

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

section Orbit

@[to_additive (attr := simp)]
theorem smul_orbit (g : G) (a : α) : g • orbit G a = orbit G a :=
  (smul_orbit_subset g a).antisymm <|
    calc
      orbit G a = g • g⁻¹ • orbit G a := (smul_inv_smul _ _).symm
      _ ⊆ g • orbit G a := Set.image_subset _ (smul_orbit_subset _ _)
#align mul_action.smul_orbit MulAction.smul_orbit
#align add_action.vadd_orbit AddAction.vadd_orbit

@[to_additive (attr := simp)]
theorem orbit_smul (g : G) (a : α) : orbit G (g • a) = orbit G a :=
  (orbit_smul_subset g a).antisymm <|
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ ⊆ orbit G (g • a) := orbit_smul_subset _ _
#align mul_action.orbit_smul MulAction.orbit_smul
#align add_action.orbit_vadd AddAction.orbit_vadd

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (a : α) : IsPretransitive G (orbit G a) :=
  ⟨by
    rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    use h * g⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
theorem orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a ∈ orbit G b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩
#align mul_action.orbit_eq_iff MulAction.orbit_eq_iff
#align add_action.orbit_eq_iff AddAction.orbit_eq_iff

@[to_additive]
theorem mem_orbit_smul (g : G) (a : α) : a ∈ orbit G (g • a) := by
  simp only [orbit_smul, mem_orbit_self]
#align mul_action.mem_orbit_smul MulAction.mem_orbit_smul
#align add_action.mem_orbit_vadd AddAction.mem_orbit_vadd

@[to_additive]
theorem smul_mem_orbit_smul (g h : G) (a : α) : g • a ∈ orbit G (h • a) := by
  simp only [orbit_smul, mem_orbit]
#align mul_action.smul_mem_orbit_smul MulAction.smul_mem_orbit_smul
#align add_action.vadd_mem_orbit_vadd AddAction.vadd_mem_orbit_vadd

@[to_additive]
lemma orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a ⊆ orbit G a :=
  orbit_submonoid_subset H.toSubmonoid a

@[to_additive]
lemma mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a ∈ orbit H b) :
    a ∈ orbit G b :=
  orbit_subgroup_subset H _ h

@[to_additive]
lemma mem_orbit_symm {a₁ a₂ : α} : a₁ ∈ orbit G a₂ ↔ a₂ ∈ orbit G a₁ := by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]
lemma mem_subgroup_orbit_iff {H : Subgroup G} {x : α} {a b : orbit G x} :
    a ∈ MulAction.orbit H b ↔ (a : α) ∈ MulAction.orbit H (b : α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, rfl⟩
    simp_rw [Submonoid.smul_def, Subgroup.coe_toSubmonoid, orbit.coe_smul, ← Submonoid.smul_def]
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    simp_rw [Submonoid.smul_def, Subgroup.coe_toSubmonoid, ← orbit.coe_smul,
             ← Submonoid.smul_def, ← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

variable (G α)

/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv :=
    ⟨mem_orbit_self, fun {a b} => by simp [orbit_eq_iff.symm, eq_comm], fun {a b} => by
      simp (config := { contextual := true }) [orbit_eq_iff.symm, eq_comm]⟩
#align mul_action.orbit_rel MulAction.orbitRel
#align add_action.orbit_rel AddAction.orbitRel

variable {G α}

@[to_additive]
theorem orbitRel_apply {a b : α} : (orbitRel G α).Rel a b ↔ a ∈ orbit G b :=
  Iff.rfl
#align mul_action.orbit_rel_apply MulAction.orbitRel_apply
#align add_action.orbit_rel_apply AddAction.orbitRel_apply

@[to_additive]
lemma orbitRel_subgroup_le (H : Subgroup G) : orbitRel H α ≤ orbitRel G α :=
  Setoid.le_def.2 mem_orbit_of_mem_orbit_subgroup

/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/
@[to_additive
      "When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the
      union of the orbit of `U` under `G`."]
theorem quotient_preimage_image_eq_union_mul (U : Set α) :
    letI := orbitRel G α
    Quotient.mk' ⁻¹' (Quotient.mk' '' U) = ⋃ g : G, (g • ·) '' U := by
  letI := orbitRel G α
  set f : α → Quotient (MulAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g • a, hb, inv_smul_smul g a⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨g, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image]
    refine ⟨g⁻¹ • a, ?_, by simp only [f, Quotient.eq']; use g⁻¹⟩
    rw [← hu₂]
    convert hu₁
    simp only [inv_smul_smul]
#align mul_action.quotient_preimage_image_eq_union_mul MulAction.quotient_preimage_image_eq_union_mul
#align add_action.quotient_preimage_image_eq_union_add AddAction.quotient_preimage_image_eq_union_add

@[to_additive]
theorem disjoint_image_image_iff {U V : Set α} :
    letI := orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V := by
  letI := orbitRel G α
  set f : α → Quotient (MulAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g • a, g_in_V, rfl⟩⟩, ?_⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb₁, hb₂⟩ ⟨c, hc₁, hc₂⟩
    obtain ⟨g, rfl⟩ := Quotient.exact (hc₂.trans hb₂.symm)
    exact h b hb₁ g hc₁
#align mul_action.disjoint_image_image_iff MulAction.disjoint_image_image_iff
#align add_action.disjoint_image_image_iff AddAction.disjoint_image_image_iff

@[to_additive]
theorem image_inter_image_iff (U V : Set α) :
    letI := orbitRel G α
    Quotient.mk' '' U ∩ Quotient.mk' '' V = ∅ ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff
#align mul_action.image_inter_image_iff MulAction.image_inter_image_iff
#align add_action.image_inter_image_iff AddAction.image_inter_image_iff

variable (G α)

/-- The quotient by `MulAction.orbitRel`, given a name to enable dot notation. -/
@[to_additive (attr := reducible)
    "The quotient by `AddAction.orbitRel`, given a name to enable dot notation."]
def orbitRel.Quotient : Type _ :=
  _root_.Quotient <| orbitRel G α
#align mul_action.orbit_rel.quotient MulAction.orbitRel.Quotient
#align add_action.orbit_rel.quotient AddAction.orbitRel.Quotient

/-- An action is pretransitive if and only if the quotient by `MulAction.orbitRel` is a
subsingleton. -/
@[to_additive "An additive action is pretransitive if and only if the quotient by
`AddAction.orbitRel` is a subsingleton."]
theorem pretransitive_iff_subsingleton_quotient :
    IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α) := by
  refine ⟨fun _ ↦ ⟨fun a b ↦ ?_⟩, fun _ ↦ ⟨fun a b ↦ ?_⟩⟩
  · refine Quot.inductionOn a (fun x ↦ ?_)
    exact Quot.inductionOn b (fun y ↦ Quot.sound <| exists_smul_eq G y x)
  · have h : Quotient.mk (orbitRel G α) b = ⟦a⟧ := Subsingleton.elim _ _
    exact Quotient.eq_rel.mp h

/-- If `α` is non-empty, an action is pretransitive if and only if the quotient has exactly one
element. -/
@[to_additive "If `α` is non-empty, an additive action is pretransitive if and only if the
quotient has exactly one element."]
theorem pretransitive_iff_unique_quotient_of_nonempty [Nonempty α] :
    IsPretransitive G α ↔ Nonempty (Unique <| orbitRel.Quotient G α) := by
  rw [unique_iff_subsingleton_and_nonempty, pretransitive_iff_subsingleton_quotient, iff_self_and]
  exact fun _ ↦ (nonempty_quotient_iff _).mpr inferInstance

variable {G α}

/-- The orbit corresponding to an element of the quotient by `MulAction.orbitRel` -/
@[to_additive "The orbit corresponding to an element of the quotient by `AddAction.orbitRel`"]
nonrec def orbitRel.Quotient.orbit (x : orbitRel.Quotient G α) : Set α :=
  Quotient.liftOn' x (orbit G) fun _ _ => MulAction.orbit_eq_iff.2
#align mul_action.orbit_rel.quotient.orbit MulAction.orbitRel.Quotient.orbit
#align add_action.orbit_rel.quotient.orbit AddAction.orbitRel.Quotient.orbit

@[to_additive (attr := simp)]
theorem orbitRel.Quotient.orbit_mk (a : α) :
    orbitRel.Quotient.orbit (Quotient.mk'' a : orbitRel.Quotient G α) = MulAction.orbit G a :=
  rfl
#align mul_action.orbit_rel.quotient.orbit_mk MulAction.orbitRel.Quotient.orbit_mk
#align add_action.orbit_rel.quotient.orbit_mk AddAction.orbitRel.Quotient.orbit_mk

@[to_additive]
theorem orbitRel.Quotient.mem_orbit {a : α} {x : orbitRel.Quotient G α} :
    a ∈ x.orbit ↔ Quotient.mk'' a = x := by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl
#align mul_action.orbit_rel.quotient.mem_orbit MulAction.orbitRel.Quotient.mem_orbit
#align add_action.orbit_rel.quotient.mem_orbit AddAction.orbitRel.Quotient.mem_orbit

/-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/
@[to_additive "Note that `hφ = Quotient.out_eq'` is a useful choice here."]
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient G α)
    {φ : orbitRel.Quotient G α → α} (hφ : letI := orbitRel G α; RightInverse φ Quotient.mk') :
    orbitRel.Quotient.orbit x = MulAction.orbit G (φ x) := by
  conv_lhs => rw [← hφ x]
  rfl
#align mul_action.orbit_rel.quotient.orbit_eq_orbit_out MulAction.orbitRel.Quotient.orbit_eq_orbit_out
#align add_action.orbit_rel.quotient.orbit_eq_orbit_out AddAction.orbitRel.Quotient.orbit_eq_orbit_out

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `MulAction.orbitRel.Quotient.orbit` instead of
`MulAction.orbit`, to avoid mentioning `Quotient.out'`. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group action.

      This version is expressed in terms of `AddAction.orbitRel.Quotient.orbit` instead of
      `AddAction.orbit`, to avoid mentioning `Quotient.out'`. "]
def selfEquivSigmaOrbits' : α ≃ Σω : Ω, ω.orbit :=
  letI := orbitRel G α
  calc
    α ≃ Σω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm
#align mul_action.self_equiv_sigma_orbits' MulAction.selfEquivSigmaOrbits'
#align add_action.self_equiv_sigma_orbits' AddAction.selfEquivSigmaOrbits'

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
      action."]
def selfEquivSigmaOrbits : α ≃ Σω : Ω, orbit G ω.out' :=
  (selfEquivSigmaOrbits' G α).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits MulAction.selfEquivSigmaOrbits
#align add_action.self_equiv_sigma_orbits AddAction.selfEquivSigmaOrbits

end Orbit

section Stabilizer
variable (G)

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.
      An additive subgroup."]
def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }
#align mul_action.stabilizer MulAction.stabilizer
#align add_action.stabilizer AddAction.stabilizer

variable {G}

@[to_additive]
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizer G a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
theorem mem_stabilizer_iff {a : α} {g : G} : g ∈ stabilizer G a ↔ g • a = a :=
  Iff.rfl
#align mul_action.mem_stabilizer_iff MulAction.mem_stabilizer_iff
#align add_action.mem_stabilizer_iff AddAction.mem_stabilizer_iff

@[to_additive]
lemma le_stabilizer_smul_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) :
    stabilizer G a ≤ stabilizer G (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

@[to_additive]
lemma le_stabilizer_smul_right [SMul α β] [SMulCommClass G α β] (a : α) (b : β) :
    stabilizer G b ≤ stabilizer G (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]
lemma stabilizer_smul_eq_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
    (h : Injective (· • b : α → β)) : stabilizer G (a • b) = stabilizer G a := by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha ↦ ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[to_additive (attr := simp)]
lemma stabilizer_smul_eq_right [Group α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β) :
    stabilizer G (a • b) = stabilizer G b :=
  (le_stabilizer_smul_right _ _).antisymm' <| (le_stabilizer_smul_right a⁻¹ _).trans_eq <| by
    rw [inv_smul_smul]

@[to_additive (attr := simp)]
lemma stabilizer_mul_eq_left [Group α] [IsScalarTower G α α] (a b : α)  :
    stabilizer G (a * b) = stabilizer G a := stabilizer_smul_eq_left a _ <| mul_left_injective _

@[to_additive (attr := simp)]
lemma stabilizer_mul_eq_right [Group α] [SMulCommClass G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G b := stabilizer_smul_eq_right a _

/-- If the stabilizer of `a` is `S`, then the stabilizer of `g • a` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g • a) = (stabilizer G a).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_inv,
    one_smul, ← mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
#align mul_action.stabilizer_smul_eq_stabilizer_map_conj MulAction.stabilizer_smul_eq_stabilizer_map_conj

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : (orbitRel G α).Rel a b) :
    stabilizer G a ≃* stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g • b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer G b).symm
#align mul_action.stabilizer_equiv_stabilizer_of_orbit_rel MulAction.stabilizerEquivStabilizerOfOrbitRel

end Stabilizer

end MulAction

namespace AddAction
variable {G α : Type*} [AddGroup G] [AddAction G α]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : G) (a : α) :
    stabilizer G (g +ᵥ a) = (stabilizer G a).map (AddAut.conj g).toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd,
    add_left_neg, zero_vadd, ← mem_stabilizer_iff, AddSubgroup.mem_map_equiv,
    AddAut.conj_symm_apply]
#align add_action.stabilizer_vadd_eq_stabilizer_map_conj AddAction.stabilizer_vadd_eq_stabilizer_map_conj

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {a b : α} (h : (orbitRel G α).Rel a b) :
    stabilizer G a ≃+ stabilizer G b :=
  let g : G := Classical.choose h
  have hg : g +ᵥ b = a := Classical.choose_spec h
  have this : stabilizer G a = (stabilizer G b).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer G b).symm
#align add_action.stabilizer_equiv_stabilizer_of_orbit_rel AddAction.stabilizerEquivStabilizerOfOrbitRel

end AddAction

attribute [to_additive existing] MulAction.stabilizer_smul_eq_stabilizer_map_conj
attribute [to_additive existing] MulAction.stabilizerEquivStabilizerOfOrbitRel

theorem Equiv.swap_mem_stabilizer {α : Type*} [DecidableEq α] {S : Set α} {a b : α} :
    Equiv.swap a b ∈ MulAction.stabilizer (Equiv.Perm α) S ↔ (a ∈ S ↔ b ∈ S) := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff, ← swap_inv]
  simp_rw [Set.mem_inv_smul_set_iff, Perm.smul_def, swap_apply_def]
  exact ⟨fun h ↦ by simpa [Iff.comm] using h a, by intros; split_ifs <;> simp [*]⟩


namespace MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/-- To prove inclusion of a *subgroup* in a stabilizer, it is enough to prove inclusions.-/
theorem le_stabilizer_iff_smul_le (s : Set α) (H : Subgroup G) :
    H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s := by
  constructor
  · intro hyp g hg
    apply Eq.subset
    rw [← mem_stabilizer_iff]
    exact hyp hg
  · intro hyp g hg
    rw [mem_stabilizer_iff]
    apply subset_antisymm (hyp g hg)
    intro x hx
    use g⁻¹ • x
    constructor
    · apply hyp g⁻¹ (inv_mem hg)
      simp only [Set.smul_mem_smul_set_iff, hx]
    · simp only [smul_inv_smul]

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_smul_le (s : Set α) (hs : s.Finite) (g : G) :
    g ∈ stabilizer G s ↔ g • s ⊆ s := by
  haveI : Fintype s := Set.Finite.fintype hs
  haveI : Fintype (g • s : Set α) := Fintype.ofFinite _
  rw [mem_stabilizer_iff]
  constructor
  exact Eq.subset
  · rw [← Set.toFinset_inj, ← Set.toFinset_subset_toFinset]
    intro h
    apply Finset.eq_of_subset_of_card_le h
    apply le_of_eq
    suffices (g • s).toFinset = Finset.map ⟨_, MulAction.injective g⟩ hs.toFinset by
      rw [this, Finset.card_map, Set.toFinite_toFinset]
    rw [← Finset.coe_inj]
    simp only [Set.coe_toFinset, Set.toFinite_toFinset, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.image_smul]

/-- To prove membership to stabilizer of a *finite set*, it is enough to prove one inclusion. -/
theorem mem_stabilizer_of_finite_iff_le_smul (s : Set α) (hs : s.Finite) (g : G) :
    g ∈ stabilizer G s ↔ s ⊆ g • s := by
  rw [← @inv_mem_iff, mem_stabilizer_of_finite_iff_smul_le s hs]
  exact Set.subset_set_smul_iff.symm
