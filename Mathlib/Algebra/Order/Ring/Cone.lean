/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Tactic.Positivity.Basic

/-!
# Constructing an ordered ring from a ring with a specified positive cone.
-/

/-! ### Positive cones -/

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

namespace Ring

/-- `PositiveConeClass S R` says that `S` is a type of `PositiveCone`s in `R`. -/
class PositiveConeClass (S R : Type*) [Ring R] [SetLike S R]
    extends AddCommGroup.PositiveConeClass S R, SubsemiringClass S R : Prop

/-- A positive cone in a `Ring` is a `Subsemiring` that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of an `OrderedRing`. -/
structure PositiveCone (R : Type*) [Ring R] extends Subsemiring R where
  eq_zero_of_mem_of_neg_mem' : ∀ {a}, a ∈ carrier → -a ∈ carrier → a = 0

instance PositiveCone.instSetLike (R : Type*) [Ring R] : SetLike (PositiveCone R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance PositiveCone.instPositiveConeClass (R : Type*) [Ring R] :
    PositiveConeClass (PositiveCone R) R where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  eq_zero_of_mem_of_neg_mem {s} := s.eq_zero_of_mem_of_neg_mem'

theorem PositiveConeClass.minus_one_not_mem [Nontrivial R] [PositiveConeClass S R] : -1 ∉ C :=
  fun minus_one_mem =>
  have := eq_zero_of_mem_of_neg_mem (one_mem C) minus_one_mem; zero_ne_one' R this.symm

/-- `PositiveConeWithSquaresClass S R` says that `S` is
a type of positive cones with squares in `R`. -/
class PositiveConeWithSquaresClass (S R : Type*) [Ring R] [SetLike S R]
    extends PositiveConeClass S R : Prop where
  square_mem : ∀ (s : S) (a : R), a * a ∈ s

export Ring.PositiveConeWithSquaresClass (square_mem)

/-- A positive cone with squares in a `Ring` is a `PositiveCone` containing all squares. -/
structure PositiveConeWithSquares (R : Type*) [Ring R] extends PositiveCone R where
  square_mem' : ∀ a, a * a ∈ carrier

instance PositiveConeWithSquares.instSetLike (R : Type*) [Ring R] :
    SetLike (PositiveConeWithSquares R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance PositiveConeWithSquares.instPositiveConeWithSquaresClass (R : Type*) [Ring R] :
    PositiveConeWithSquaresClass (PositiveConeWithSquares R) R where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  eq_zero_of_mem_of_neg_mem {s} := s.eq_zero_of_mem_of_neg_mem'
  square_mem {s} := s.square_mem'

/-- `TotalPositiveConeClass S R` says that `S` is a type of `TotalPositiveCone`s in `R`. -/
class TotalPositiveConeClass (S R : Type*) [Ring R] [IsDomain R] [SetLike S R]
    extends AddCommGroup.TotalPositiveConeClass S R, PositiveConeClass S R : Prop

/-- A total positive cone in a domain is a `PositiveCone` containing
either `a` or `-a` for every `a`.
This is equivalent to being the set of non-negative elements of a `LinearOrderedRing`. -/
structure TotalPositiveCone (R : Type*) [Ring R] [IsDomain R] extends PositiveCone R where
  mem_or_neg_mem' : ∀ a, a ∈ carrier ∨ -a ∈ carrier

instance TotalPositiveCone.instSetLike (R : Type*) [Ring R] [IsDomain R] :
    SetLike (TotalPositiveCone R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance TotalPositiveCone.instTotalPositiveConeClass (R : Type*) [Ring R] [IsDomain R] :
    TotalPositiveConeClass (TotalPositiveCone R) R where
  add_mem {s} := s.add_mem'
  zero_mem {s} := s.zero_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  eq_zero_of_mem_of_neg_mem {s} := s.eq_zero_of_mem_of_neg_mem'
  mem_or_neg_mem {s} := s.mem_or_neg_mem'

instance TotalPositiveConeClass.instPositiveConeWithSquaresClass (S R : Type*)
    [Ring R] [IsDomain R] [SetLike S R] [TotalPositiveConeClass S R] :
    PositiveConeWithSquaresClass S R where
  square_mem s a := Or.elim (mem_or_neg_mem s a)
                            (fun a_mem => mul_mem a_mem a_mem)
                            (fun na_mem => by simpa using mul_mem na_mem na_mem)

end Ring

open Ring

/-- Construct an `OrderedRing` by designating a positive cone in an existing `Ring`. -/
@[reducible] def OrderedRing.mkOfPositiveCone [Ring.PositiveConeClass S R] : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfPositiveCone C
  zero_le_one := by simpa using one_mem C
  mul_nonneg x y xnn ynn := by simpa using mul_mem xnn ynn

def StrictOrderedRing. (α : Type*) [OrderedRing α] [IsDomain α] : StrictOrderedRing α where
  __ := ‹OrderedRing α›
  __ := ‹IsDomain α›
  mul_pos a b ap bp := by positivity



/-  lt_of_le_of_ne
                       (mul_nonneg (le_of_lt ap) (le_of_lt bp))
                       (mul_ne_zero_iff.mpr ⟨ne_of_gt ap, ne_of_gt bp⟩).symm -/

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
@[reducible] def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone,
    StrictOrderedRing.mkOfPositiveCone C.toPositiveCone_1 with }
