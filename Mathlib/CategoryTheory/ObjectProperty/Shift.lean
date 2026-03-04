/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Properties of objects on categories equipped with shift

Given a predicate `P : ObjectProperty C` on objects of a category equipped with a shift
by `A`, we define shifted properties of objects `P.shift a` for all `a : A`.
We also introduce a typeclass `P.IsStableUnderShift A` to say that `P X`
implies `P (X⟦a⟧)` for all `a : A`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]
  {E : Type*} [Category* E] [HasShift E A]

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

instance (a : A) [P.IsStableUnderShiftBy a]
    [Q.IsStableUnderShiftBy a] : (P ⊓ Q).IsStableUnderShiftBy a where
  le_shift _ hX :=
    ⟨P.le_shift a _ hX.1, Q.le_shift a _ hX.2⟩

variable (A) in
/-- `P : ObjectProperty C` is stable under the shift by `A` if
`P X` implies `P X⟦a⟧` for any `a : A`. -/
class IsStableUnderShift where
  isStableUnderShiftBy (a : A) : P.IsStableUnderShiftBy a := by infer_instance

attribute [instance] IsStableUnderShift.isStableUnderShiftBy

instance [P.IsStableUnderShift A] :
    P.isoClosure.IsStableUnderShift A where

instance [P.IsStableUnderShift A]
    [Q.IsStableUnderShift A] : (P ⊓ Q).IsStableUnderShift A where

lemma prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C G]
    [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) :
    P (X⟦g⟧) ↔ P X := by
  refine ⟨fun hX ↦ ?_, P.le_shift g _⟩
  rw [← P.shift_zero G, ← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

variable (A) in
/-- The closure by shifts and isomorphism of a predicate on objects in a category. -/
def shiftClosure : ObjectProperty C := fun X => ∃ (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y

lemma prop_shiftClosure_iff (X : C) :
    shiftClosure P A X ↔ ∃ (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y := Iff.rfl

lemma le_shiftClosure : P ≤ P.shiftClosure A := by
  intro X hX
  exact ⟨X, 0, (shiftFunctorZero C A).symm.app X, hX⟩

variable {P Q} in
lemma monotone_shiftClosure (h : P ≤ Q) : P.shiftClosure A ≤ Q.shiftClosure A := by
  rintro X ⟨Y, a, i, hY⟩
  refine ⟨Y, a, i, h Y hY⟩

lemma shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] :
    P.shiftClosure A = P := by
  refine le_antisymm ?_ P.le_shiftClosure
  rintro X ⟨Y, a, i, hY⟩
  exact P.prop_of_iso i.symm (P.le_shift a Y hY)

lemma shiftClosure_le_iff [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A] :
    shiftClosure P A ≤ Q ↔ P ≤ Q :=
  ⟨(le_shiftClosure P).trans,
    fun h => (monotone_shiftClosure h).trans (by rw [shiftClosure_eq_self])⟩

instance : (P.shiftClosure A).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y i ⟨Z, a, i', hZ⟩
    exact ⟨Z, a, i.symm.trans i', hZ⟩

instance (a : A) : (P.shiftClosure A).IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, b, i, hY⟩
    exact ⟨Y, b + a, ((shiftFunctor C a).mapIso i).trans <|
      (shiftFunctorAdd C b a).symm.app Y, hY⟩

instance : (P.shiftClosure A).IsStableUnderShift A where

lemma isStableUnderShift_iff_shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] :
    IsStableUnderShift P A ↔ shiftClosure P A = P :=
  ⟨fun _ ↦ shiftClosure_eq_self _, fun h ↦ by rw [← h]; infer_instance⟩


variable [P.IsStableUnderShift A]

noncomputable instance hasShift :
    HasShift P.FullSubcategory A :=
  P.fullyFaithfulι.hasShift (fun n ↦ ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X ↦ P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)

instance commShiftι : P.ι.CommShift A :=
  Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent any abuse of defeq
#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12247
this requires `allowUnsafeReducibility`. -/
set_option allowUnsafeReducibility true in
attribute [irreducible] hasShift commShiftι

section

variable (F : E ⥤ C) (hF : ∀ (X : E), P (F.obj X))

noncomputable instance [F.CommShift A] :
    (P.lift F hF).CommShift A :=
  Functor.CommShift.ofComp (P.liftCompιIso F hF) A

noncomputable instance [F.CommShift A] :
    NatTrans.CommShift (P.liftCompιIso F hF).hom A :=
  Functor.CommShift.ofComp_compatibility _ _

end

instance [P.IsClosedUnderIsomorphisms] (F : E ⥤ C) [F.CommShift A] :
    (P.inverseImage F).IsStableUnderShift A where
  isStableUnderShiftBy n :=
    { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }

end ObjectProperty

end CategoryTheory
