/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# Construct ordered groups from positive cones

In this file we provide structures `PositiveCone` and `TotalPositiveCone`
that encode axioms of `OrderedAddCommGroup` and `LinearOrderedAddCommGroup`
in terms of the subset of non-negative elements.

We also provide two constructors,
`OrderedAddCommGroup.mkOfPositiveCone` and `LinearOrderedAddCommGroup.mkOfPositiveCone`,
that turn these structures into instances of the corresponding typeclasses.
-/

universe u v w

namespace AddCommGroup

/-- A collection of elements in an `AddCommGroup` designated as "non-negative".
This induces an `OrderedAddCommGroup`. -/
class PositiveConeClass (S : Type u) (G : Type v) [AddCommGroup G] [SetLike S G]
    extends AddSubmonoidClass S G : Prop where
  eq_zero_of_mem_of_neg_mem : ∀ {s : S} {a : G}, a ∈ s → -a ∈ s → a = 0

export PositiveConeClass (eq_zero_of_mem_of_neg_mem)

structure PositiveCone (G : Type u) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' : ∀ {a}, a ∈ carrier → -a ∈ carrier → a = 0

instance PositiveCone.instSetLike (G : Type u) [AddCommGroup G] : SetLike (PositiveCone G) G where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance PositiveCone.instAddSubmonoidClass (G : Type u) [AddCommGroup G] :
    AddSubmonoidClass (PositiveCone G) G where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'

instance PositiveCone.instPositiveConeClass (G : Type u) [AddCommGroup G] :
    PositiveConeClass (PositiveCone G) G where
  eq_zero_of_mem_of_neg_mem {s} := s.eq_zero_of_mem_of_neg_mem'

/-- A positive cone such that, for every `a`, either `a` or `-a` is non-negative.
This indices a `LinearOrderedAddCommGroup`. -/
class TotalPositiveConeClass (S : Type u) (G : Type v) [AddCommGroup G] [SetLike S G]
    extends PositiveConeClass S G : Prop where
  mem_or_neg_mem : ∀ (s : S) (a : G), a ∈ s ∨ -a ∈ s

export TotalPositiveConeClass (mem_or_neg_mem)

structure TotalPositiveCone (G : Type u) [AddCommGroup G] extends PositiveCone G where
  mem_or_neg_mem' : ∀ a, a ∈ carrier ∨ -a ∈ carrier

instance TotalPositiveCone.instSetLike (G : Type u) [AddCommGroup G] :
  SetLike (TotalPositiveCone G) G where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance TotalPositiveCone.instPositiveConeClass (G : Type u) [AddCommGroup G] :
    PositiveConeClass (TotalPositiveCone G) G where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  eq_zero_of_mem_of_neg_mem {s} := s.eq_zero_of_mem_of_neg_mem'

instance TotalPositiveCone.instTotalPositiveConeClass (G : Type u) [AddCommGroup G] :
    TotalPositiveConeClass (TotalPositiveCone G) G where
  mem_or_neg_mem {s} := s.mem_or_neg_mem'

end AddCommGroup

namespace OrderedAddCommGroup

open AddCommGroup

/-- Construct an `OrderedAddCommGroup` by
designating a positive cone in an existing `AddCommGroup`. -/
def mkOfPositiveCone {S : Type u} {G : Type v}
    [AddCommGroup G] [SetLike S G] [PositiveConeClass S G] (C : S) :
    OrderedAddCommGroup G :=
  { ‹AddCommGroup G› with
    le := fun a b => a - b ∈ C,
    le_refl := fun a => by simp [zero_mem],
    le_trans := fun a b c nab nbc => by simpa using add_mem nbc nab,
    le_antisymm := fun a b nab nba =>
      by apply eq_of_sub_eq_zero; simp at nba; simpa [nba] using eq_zero_of_mem_of_neg_mem nab,
    add_le_add_left := fun a b nab c => by simpa using nab }

end OrderedAddCommGroup

namespace LinearOrderedAddCommGroup

open AddCommGroup

/-- Construct a `LinearOrderedAddCommGroup` by
designating a total positive cone in an existing `AddCommGroup`. -/
def mkOfPositiveCone {S : Type u} {G : Type v}
    [AddCommGroup G] [SetLike S G] [TotalPositiveConeClass S G]
    (C : S) (dec : DecidablePred (fun x => x ∈ C)) :
    LinearOrderedAddCommGroup G :=
  { OrderedAddCommGroup.mkOfPositiveCone C with
    le_total := fun a b => by simpa using mem_or_neg_mem C (a - b)
    decidableLE := fun a b => dec _ }

end LinearOrderedAddCommGroup
