/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

-/

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

/-- Construction of the naive shift on the opposite category of a category `C`:
the shiftfunctor by `n` is `(shiftFunctor C n).op`. -/
noncomputable def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift

/-- The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n).op`. -/
@[nolint unusedArguments]
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ

instance : Category (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

noncomputable instance : HasShift (OppositeShift C A) A :=
  hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

instance [HasZeroObject C] : HasZeroObject (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

instance [Preadditive C] : Preadditive (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

instance [Preadditive C] (n : A) [(shiftFunctor C n).Additive] :
    (shiftFunctor (OppositeShift C A) n).Additive := by
  change (shiftFunctor C n).op.Additive
  infer_instance

lemma oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).inv.app X =
      ((shiftFunctorZero C A).hom.app X.unop).op := rfl

lemma oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).hom.app X =
      ((shiftFunctorZero C A).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorZero_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

variable {C A}
variable (X : OppositeShift C A) (a b c : A) (h : a + b = c)

lemma oppositeShiftFunctorAdd_inv_app :
    (shiftFunctorAdd (OppositeShift C A) a b).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X.unop).op := rfl

lemma oppositeShiftFunctorAdd_hom_app :
    (shiftFunctorAdd (OppositeShift C A) a b).hom.app X =
      ((shiftFunctorAdd C a b).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorAdd_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

lemma oppositeShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).inv.app X =
      ((shiftFunctorAdd' C a b c h).hom.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

lemma oppositeShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).hom.app X =
      ((shiftFunctorAdd' C a b c h).inv.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

end CategoryTheory
