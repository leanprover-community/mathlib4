/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

We demonstrate the equivalence between order structures on a group `G` and *positive cones*:
submonoids `M` of `G` such that `M ∩ -M = 0`.

-/

@[expose] public section

variable (G : Type*) [CommGroup G]

@[to_additive]
theorem Submonoid.oneLE.isMulPointed [PartialOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulPointed := by aesop (add simp ge_antisymm_iff)

@[to_additive]
theorem Submonoid.oneLE.isMulSpanning [LinearOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulSpanning := by aesop (add safe le_total)

variable {G} {M : Submonoid G} (hM : M.IsMulPointed)

/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a partial order by designating a submonoid with zero support in an abelian group. -/]
abbrev PartialOrder.mkOfSubmonoid : PartialOrder G where
  le a b := b / a ∈ M
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using hM.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

variable {hM} in
@[to_additive (attr := simp)]
theorem PartialOrder.mkOfSubmonoid_le_iff {a b : G} :
    (mkOfSubmonoid hM).le a b ↔ b / a ∈ M := .rfl

@[to_additive]
theorem IsOrderedMonoid.mkOfSubmonoid :
    letI _ := PartialOrder.mkOfSubmonoid hM
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid hM
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }

/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/
@[to_additive
/-- Construct a linear order by designating
    a maximal submonoid with zero support in an abelian group. -/]
abbrev LinearOrder.mkOfSubmonoid (hMs : M.IsMulSpanning) [DecidablePred (· ∈ M)] :
    LinearOrder G where
  __ := PartialOrder.mkOfSubmonoid hM
  le_total a b := by simpa using hMs.mem_or_inv_mem (b / a)
  toDecidableLE _ := _

/-- `AddGroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[deprecated "Unbundled to `AddSubmonoid.IsPointed`" (since := "2026-03-28")]
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

set_option linter.existingAttributeWarning false in
/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive, deprecated "Unbundled to `Submonoid.IsMulPointed`" (since := "2026-03-28")]
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] : Prop
    extends SubmonoidClass S G where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
@[deprecated "Unbundled to `AddSubmonoid.IsPointed`" (since := "2026-03-28")]
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

set_option linter.existingAttributeWarning false in
/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive, deprecated "Unbundled to `Submonoid.IsMulPointed`" (since := "2026-03-28")]
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1

@[to_additive (attr := deprecated "no replacement" (since := "2026-03-28"))]
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive (attr := deprecated "no replacement" (since := "2026-03-28"))]
instance (G : Type*) [CommGroup G] : PartialOrder (GroupCone G) := .ofSetLike (GroupCone G) G

@[to_additive (attr := deprecated "no replacement" (since := "2026-03-28"))]
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier → coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier → coe, as_prefix coe)

namespace GroupCone
variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

variable (H) in
/-- The cone of elements that are at least 1. -/
@[to_additive (attr := deprecated Submonoid.oneLE.isMulPointed (since := "2026-03-28"))
/-- The cone of non-negative elements. -/]
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp, deprecated "no replacement" (since := "2026-03-28"))]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp, deprecated "no replacement" (since := "2026-03-28"))]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast, deprecated "no replacement" (since := "2026-03-28"))]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

@[to_additive (attr := deprecated Submonoid.oneLE.isMulSpanning (since := "2026-03-28"))]
instance oneLE.hasMemOrInvMem {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H] :
    HasMemOrInvMem (oneLE H) where
  mem_or_inv_mem := by simpa using le_total 1

end GroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive (attr := deprecated PartialOrder.mkOfSubmonoid (since := "2026-03-28"))
/-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp, deprecated PartialOrder.mkOfSubmonoid_le_iff (since := "2026-03-28"))]
lemma PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := Iff.rfl

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive (attr := deprecated LinearOrder.mkOfSubmonoid (since := "2026-03-28"))
/-- Construct a linear order by designating a maximal cone in an abelian group. -/]
abbrev LinearOrder.mkOfGroupCone
    [GroupConeClass S G] [HasMemOrInvMem C] [DecidablePred (· ∈ C)] : LinearOrder G where
  __ := PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive (attr := deprecated IsOrderedMonoid.mkOfSubmonoid (since := "2026-03-28"))
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
lemma IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }
