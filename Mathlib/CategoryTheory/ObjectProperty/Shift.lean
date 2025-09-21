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
We also introduce a typeclass `P.IsStableUnderShift A` to say that `P X`
implies `P (X⟦a⟧)` for all `a : A`.

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

/-- `P : ObjectProperty C` is stable under the shift by `a : A` if
`P X` implies `P X⟦a⟧`. -/
class IsStableUnderShiftBy (a : A) : Prop where
  le_shift : P ≤ P.shift a

lemma le_shift (a : A) [P.IsStableUnderShiftBy a] :
    P ≤ P.shift a := IsStableUnderShiftBy.le_shift

instance (a : A) [P.IsStableUnderShiftBy a] :
    P.isoClosure.IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨(shiftFunctor C a).mapIso e⟩⟩

variable (A) in
/-- `P : ObjectProperty C` is stable under the shift by `A` if
`P X` implies `P X⟦a⟧` for any `a : A`. -/
class IsStableUnderShift where
  isStableUnderShiftBy (a : A) : P.IsStableUnderShiftBy a := by infer_instance

attribute [instance] IsStableUnderShift.isStableUnderShiftBy

instance [P.IsStableUnderShift A] :
    P.isoClosure.IsStableUnderShift A where

lemma prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C G]
    [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) :
    P (X⟦g⟧) ↔ P X := by
  refine ⟨fun hX ↦ ?_, P.le_shift g _⟩
  rw [← P.shift_zero G, ← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

end ObjectProperty

end CategoryTheory
