import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [hC : HasShift C A]

namespace HasShift

noncomputable def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X := by
    apply Opposite.unop_injective
    refine' (shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans _
    dsimp [shiftFunctorAdd']
    -- why does not `rw [unop_comp]` work?
    change _ = (_ ≫ _) ≫ _
    simp only [eqToHom_app, Opposite.unop_op, Quiver.Hom.unop_op, eqToHom_unop, Category.assoc]
  zero_add_hom_app n X := by
    apply Opposite.unop_injective
    refine' (shiftFunctorAdd_zero_add_inv_app n X.unop).trans _
    dsimp
    change _ = _ ≫ _
    simp only [Quiver.Hom.unop_op, eqToHom_unop]
  add_zero_hom_app n X := by
    apply Opposite.unop_injective
    refine' (shiftFunctorAdd_add_zero_inv_app n X.unop).trans _
    dsimp
    change _ = _ ≫ _
    simp only [Quiver.Hom.unop_op, eqToHom_unop]

noncomputable def op : HasShift Cᵒᵖ A :=
  hasShiftMk Cᵒᵖ A (mkShiftCoreOp C A)

end HasShift

@[nolint unusedArguments]
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ

instance : Category (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

noncomputable instance : HasShift (OppositeShift C A) A :=
  HasShift.op C A

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

end CategoryTheory
