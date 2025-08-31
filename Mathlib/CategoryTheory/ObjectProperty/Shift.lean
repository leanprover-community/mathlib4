/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Shift.Basic

/-!
# Properties of objects on categories equipped with shift

Given a predicate `P : ObjectProperty C` on objects of a category equipped with a shift
by `A`, we define shifted properties of objects `P.shift a` for all `a : A`.

-/

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category C] (P : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]

namespace ObjectProperty

/-- Given a predicate `P : C → Prop` on objects of a category equipped with a shift by `A`,
this is the predicate which is satisfied by `X` if `P (X⟦a⟧)`. -/
def shift (a : A) : ObjectProperty C := fun X => P (X⟦a⟧)

lemma prop_shift_iff (a : A) (X : C) : P.shift a X ↔ P (X⟦a⟧) := Iff.rfl

instance (a : A) [P.IsClosedUnderIsomorphisms] :
    (P.shift a).IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
lemma shift_zero [P.IsClosedUnderIsomorphisms] : P.shift (0 : A) = P := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

variable {A}

lemma shift_shift (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms] :
    (P.shift b).shift a = P.shift c := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)

end ObjectProperty

@[deprecated (since := "2025-02-25")] alias PredicateShift := ObjectProperty.shift
@[deprecated (since := "2025-02-25")] alias predicateShift_iff := ObjectProperty.prop_shift_iff
@[deprecated (since := "2025-02-25")] alias predicateShift_zero := ObjectProperty.shift_zero
@[deprecated (since := "2025-02-25")] alias predicateShift_predicateShift :=
  ObjectProperty.shift_shift

end CategoryTheory
