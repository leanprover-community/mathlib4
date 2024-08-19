/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

-/


/-! ### Positive cones -/

variable {R : Type*} [Ring R]

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

/-- `PositiveConeWithSquaresClass S R` says that `S` is
a type of positive cones with squares in `R`. -/
class PositiveConeWithSquaresClass (S R : Type*) [Ring R] [SetLike S R]
    extends PositiveConeClass S R : Prop where
  square_mem : ∀ (s : S) (a : R), a * a ∈ s

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

instance TotalPositiveCone.instPositiveConeWithSquaresClass (R : Type*) [Ring R] [IsDomain R] :
    PositiveConeWithSquaresClass (TotalPositiveCone R) R where
  square_mem := by

end Ring

open Ring

/-- Construct a `StrictOrderedRing` by designating a positive cone in an existing `Ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩,
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp,
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      -- Porting note: used to be convert, but it relied on unfolding definitions
      rw [sub_zero]
      exact C.mul_pos x y (by rwa [← sub_zero x]) (by rwa [← sub_zero y]) }

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone,
    StrictOrderedRing.mkOfPositiveCone C.toPositiveCone_1 with }
