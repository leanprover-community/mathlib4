/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Artie Khovanov
-/
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide the structure `GroupCone` and the predicate `IsMaxCone`
that encode axioms of `OrderedCommGroup` and `LinearOrderedCommGroup`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

/-- `AddGroupConeClass S G` says that `S` is a type of cones in `G`. -/
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] : Prop
    extends SubmonoidClass S G where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive]
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1

@[to_additive]
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier → coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier → coe, as_prefix coe)

/-- Typeclass for maximal additive cones. -/
class IsMaxCone {S G : Type*} [AddCommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_neg_mem' (a : G) : a ∈ C ∨ -a ∈ C

/-- Typeclass for maximal multiplicative cones. -/
@[to_additive IsMaxCone]
class IsMaxMulCone {S G : Type*} [CommGroup G] [SetLike S G] (C : S) : Prop where
  mem_or_inv_mem' (a : G) : a ∈ C ∨ a⁻¹ ∈ C

@[to_additive]
lemma mem_or_inv_mem {S G : Type*} [CommGroup G] [SetLike S G] (C : S) [IsMaxMulCone C]
    (a : G) : a ∈ C ∨ a⁻¹ ∈ C := IsMaxMulCone.mem_or_inv_mem' a

namespace GroupCone
variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

variable (H) in
/-- The cone of elements that are at least 1. -/
@[to_additive /-- The cone of non-negative elements. -/]
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp)]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp)]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast)]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

@[to_additive nonneg.isMaxCone]
instance oneLE.isMaxMulCone {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H] :
    IsMaxMulCone (oneLE H) where
  mem_or_inv_mem' := by simpa using le_total 1

end GroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
lemma PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := Iff.rfl

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
abbrev LinearOrder.mkOfGroupCone
    [GroupConeClass S G] [IsMaxMulCone C] [DecidablePred (· ∈ C)] : LinearOrder G where
  __ := PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
lemma IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }
