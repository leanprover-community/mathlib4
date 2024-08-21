/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.Algebra.Ring.Semireal.Defs

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
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance PositiveCone.instPositiveConeClass (R : Type*) [Ring R] :
    PositiveConeClass (PositiveCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

theorem PositiveConeClass.minus_one_not_mem [Nontrivial R] [PositiveConeClass S R] : -1 ∉ C :=
  fun minus_one_mem =>
  have := eq_zero_of_mem_of_neg_mem (one_mem C) minus_one_mem; zero_ne_one' R this.symm

/-- `PositiveConeWithSquaresClass S R` says that `S` is
a type of positive cones with squares in `R`. -/
class PositiveConeWithSquaresClass (S R : Type*) [Ring R] [SetLike S R]
    extends PositiveConeClass S R : Prop where
  square_mem : ∀ (C : S) (a : R), a * a ∈ C

export Ring.PositiveConeWithSquaresClass (square_mem)

/-- A positive cone with squares in a `Ring` is a `PositiveCone` containing all squares. -/
structure PositiveConeWithSquares (R : Type*) [Ring R] extends PositiveCone R where
  square_mem' : ∀ a, a * a ∈ carrier

instance PositiveConeWithSquares.instSetLike (R : Type*) [Ring R] :
    SetLike (PositiveConeWithSquares R) R where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance PositiveConeWithSquares.instPositiveConeWithSquaresClass (R : Type*) [Ring R] :
    PositiveConeWithSquaresClass (PositiveConeWithSquares R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'
  square_mem {C} := C.square_mem'

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
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance TotalPositiveCone.instTotalPositiveConeClass (R : Type*) [Ring R] [IsDomain R] :
    TotalPositiveConeClass (TotalPositiveCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'
  mem_or_neg_mem {C} := C.mem_or_neg_mem'

instance TotalPositiveConeClass.instPositiveConeWithSquaresClass (S R : Type*)
    [Ring R] [IsDomain R] [SetLike S R] [TotalPositiveConeClass S R] :
    PositiveConeWithSquaresClass S R where
  square_mem C a := Or.elim (mem_or_neg_mem C a)
                            (fun a_mem => mul_mem a_mem a_mem)
                            (fun na_mem => by simpa using mul_mem na_mem na_mem)

namespace PositiveCone
variable {T : Type*} [OrderedRing T] {a : T}

variable (T) in
/-- Construct a `PositiveCone` from
the set of positive elements of an existing `OrderedRing`. -/
def nonneg : PositiveCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

end PositiveCone

namespace TotalPositiveCone
variable {T : Type*} [LinearOrderedRing T] {a : T}

variable (T) in
/-- Construct a `TotalPositiveCone` from
the set of positive elements of an existing `LinearOrderedRing`. -/
def nonneg : TotalPositiveCone T where
  __ := PositiveCone.nonneg T
  mem_or_neg_mem' := by simpa using le_total 0

@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
@[simp] lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl

end Ring.TotalPositiveCone

open Ring

/-- Construct an `OrderedRing` by designating a positive cone in an existing `Ring`. -/
@[reducible] def OrderedRing.mkOfPositiveCone [PositiveConeClass S R] : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfPositiveCone C
  zero_le_one := show _ ∈ C by simpa using one_mem C
  mul_nonneg x y xnn ynn := show _ ∈ C by simpa using mul_mem xnn ynn

def OrderedRing.toStrictOrderedRing (α : Type*) [OrderedRing α] [IsDomain α] :
    StrictOrderedRing α where
  __ := ‹OrderedRing α›
  __ := ‹IsDomain α›
  mul_pos a b ap bp := lt_of_le_of_ne
                       (mul_nonneg (le_of_lt ap) (le_of_lt bp))
                       (mul_ne_zero_iff.mpr ⟨ne_of_gt ap, ne_of_gt bp⟩).symm

/- this should work but it doesn't -/
/- by have := (mul_ne_zero_iff (M₀ := α) (a := a) (b := b)).mpr; positivity -/

/-- Construct a `LinearOrderedRing` by
designating a positive cone in an existing `Ring`. -/
@[reducible] def LinearOrderedRing.mkOfPositiveCone
    [IsDomain R] [TotalPositiveConeClass S R] (dec : DecidablePred (fun x => x ∈ C)) :
    LinearOrderedRing R where
  __ := OrderedRing.mkOfPositiveCone C
  __ := OrderedRing.toStrictOrderedRing R
  le_total a b := by simpa using mem_or_neg_mem C (b - a)
  decidableLE a b := dec _

/- TODO : relax typeclass (should really be in SumOfSquares file)-/
def sumSqIn' (T : Type*) [Ring T] : Subsemiring T where
  __ := sumSqIn T
  mul_mem' := sorry
  one_mem' := by simp; apply mem_sumSqIn_of_isSquare; simp

def SemirealRing.sumSqIn [IsSemireal R] : PositiveCone R where
  __ := sumSqIn' R
  eq_zero_of_mem_of_neg_mem' := sorry
