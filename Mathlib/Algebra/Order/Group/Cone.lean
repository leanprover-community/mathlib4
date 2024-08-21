/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide structures `GroupCone` and `MaximalGroupCone`
that encode axioms of `OrderedCommGroup` and `LinearOrderedCommGroup`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

variable {S G : Type*} [AddCommGroup G] [SetLike S G] (C : S)

namespace AddCommGroup

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
class GroupConeClass (S G : Type*) [AddCommGroup G] [SetLike S G]
    extends AddSubmonoidClass S G : Prop where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

export GroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
structure GroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

instance GroupCone.instSetLike (G : Type*) [AddCommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance GroupCone.instGroupConeClass (G : Type*) [AddCommGroup G] :
    GroupConeClass (GroupCone G) G where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

/-- `MaximalGroupConeClass S G` says that `S` is a type of maximal cones in `G`. -/
class MaximalGroupConeClass (S G : Type*) [AddCommGroup G] [SetLike S G]
    extends GroupConeClass S G : Prop where
  mem_or_neg_mem (C : S) (a : G) : a ∈ C ∨ -a ∈ C

export MaximalGroupConeClass (mem_or_neg_mem)

/-- A maximal (positive) cone in an abelian group is a cone containing
either `a` or `-a` for every `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a linearly ordered group. -/
structure MaximalGroupCone (G : Type*) [AddCommGroup G] extends GroupCone G where
  mem_or_neg_mem' a : a ∈ carrier ∨ -a ∈ carrier

instance MaximalGroupCone.instSetLike (G : Type*) [AddCommGroup G] :
  SetLike (MaximalGroupCone G) G where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance MaximalGroupCone.instGroupConeClass (G : Type*) [AddCommGroup G] :
    GroupConeClass (MaximalGroupCone G) G where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

instance MaximalGroupCone.instMaximalGroupConeClass (G : Type*) [AddCommGroup G] :
    MaximalGroupConeClass (MaximalGroupCone G) G where
  mem_or_neg_mem {C} := C.mem_or_neg_mem'

namespace GroupCone
variable {H : Type*} [OrderedAddCommGroup H] {a : H}

variable (H) in
/-- Construct a cone from the set of non-negative elements of a partially ordered abelian group. -/
def nonneg : GroupCone H where
  __ := AddSubmonoid.nonneg H
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp] lemma nonneg_toAddSubmonoid : (nonneg H).toAddSubmonoid = .nonneg H := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg H ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg H = {x : H | 0 ≤ x} := rfl

end GroupCone

namespace MaximalGroupCone
variable {H : Type*} [LinearOrderedAddCommGroup H] {a : H}

variable (H) in
/-- Construct a maximal cone from the set of non-negative elements of
a linearly ordered abelian group. -/
def nonneg : MaximalGroupCone H where
  __ := GroupCone.nonneg H
  mem_or_neg_mem' := by simpa using le_total 0

@[simp] lemma nonneg_toAddSubmonoid : (nonneg H).toAddSubmonoid = .nonneg H := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg H ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg H = {x : H | 0 ≤ x} := rfl

end AddCommGroup.MaximalGroupCone

export AddCommGroup (eq_zero_of_mem_of_neg_mem)
export AddCommGroup (mem_or_neg_mem)

open AddCommGroup

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[reducible] def OrderedAddCommGroup.mkOfPositiveCone [GroupConeClass S G] :
    OrderedAddCommGroup G where
  le a b := b - a ∈ C
  le_refl a := by simp [zero_mem]
  le_trans a b c nab nbc := by simpa using add_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [sub_eq_zero, eq_comm] using eq_zero_of_mem_of_neg_mem nab (by simpa using nba)
  add_le_add_left a b nab c := by simpa using nab

/-- Construct a linearly ordered abelian group by
designating a maximal cone in an abelian group. -/
@[reducible] def LinearOrderedAddCommGroup.mkOfPositiveCone
    [MaximalGroupConeClass S G] (dec : DecidablePred (· ∈ C)) :
    LinearOrderedAddCommGroup G where
  __ := OrderedAddCommGroup.mkOfPositiveCone C
  le_total a b := by simpa using mem_or_neg_mem C (b - a)
  decidableLE a b := dec _
