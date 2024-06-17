/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Triangulated.Opposite
import Mathlib.CategoryTheory.Shift.ShiftedHom

-- should be moved
/-- The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`. -/
@[simps]
def Quiver.Hom.opEquiv {V : Type*} [Quiver V] {X Y : V} :
    (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

namespace CategoryTheory

open Category Pretriangulated.Opposite Pretriangulated

variable {C : Type*} [Category C] [HasShift C ℤ] {X Y Z : C}

namespace ShiftedHom

/-- The bijection `ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n` when
`n : ℤ`, and `X` and `Y` are objects of a category equipped with a shift by `ℤ`. -/
noncomputable def opEquiv (n : ℤ) :
    ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n :=
  Quiver.Hom.opEquiv.trans
    ((opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv (Opposite.op Y) (Opposite.op X))

lemma opEquiv_symm_apply {n : ℤ} (f : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm f =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app (Opposite.op X)).unop ≫ f.unop⟦n⟧' := by
  rfl

/-- The bijection `ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)`
when integers `n`, `a` and `a'` satisfy `n + a = a'`, and `X` and `Y` are objects
of a category equipped with a shift by `ℤ`. -/
noncomputable def opEquiv' (n a a' : ℤ) (h : n + a = a') :
    ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧) :=
  ((shiftFunctorAdd' C a n a' (by omega)).symm.app Y).homToEquiv.symm.trans (opEquiv n)

lemma opEquiv'_symm_apply {n a : ℤ} (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm f =
      (opEquiv n).symm f ≫ (shiftFunctorAdd' C a n a' (by omega)).inv.app _ :=
  rfl

lemma opEquiv'_symm_op_opShiftFunctorEquivalence_counitIso_inv_app_op_shift
    {n m : ℤ} (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m)
    (q : ℤ) (hq : n + m = q) :
    (opEquiv' n m q hq).symm
        (g.op ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app _ ≫ f.op⟦n⟧') =
      f.comp g (by omega) := by
  rw [opEquiv'_symm_apply, opEquiv_symm_apply]
  dsimp [comp]
  apply Quiver.Hom.op_inj
  simp only [assoc, Functor.map_comp, op_comp, Quiver.Hom.op_unop,
    opShiftFunctorEquivalence_unitIso_inv_naturality]
  erw [(opShiftFunctorEquivalence C n).inverse_counitInv_comp_assoc (Opposite.op Y)]

lemma opEquiv'_zero_add_symm (a : ℤ) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : ℤ)⟧) :
    (opEquiv' 0 a a (zero_add a)).symm f =
      ((shiftFunctorZero Cᵒᵖ ℤ).hom.app _).unop ≫ f.unop := by
  sorry

lemma opEquiv'_symm_comp (f : Y ⟶ X) {n a : ℤ} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x ≫ f.op⟦n⟧') = f ≫ (opEquiv' n a a' h).symm x :=
  Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])

lemma opEquiv'_add_symm (n m a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦m + n⟧)) :
    (opEquiv' (m + n) a a'' (by omega)).symm x =
      (opEquiv' m a' a'' ha'').symm ((opEquiv' n a a' ha').symm
        (x ≫ (shiftFunctorAdd Cᵒᵖ m n).hom.app _)).op := by
  sorry

section Preadditive

variable [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

@[simp]
lemma opEquiv_symm_add {n : ℤ} (x y : ShiftedHom (Opposite.op Y) (Opposite.op X) n) :
    (opEquiv n).symm (x + y) = (opEquiv n).symm x + (opEquiv n).symm y := by
  dsimp [opEquiv_symm_apply]
  rw [← Preadditive.comp_add, ← Functor.map_add]
  rfl

@[simp]
lemma opEquiv'_symm_add {n a : ℤ} (x y : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧))
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x + y) =
      (opEquiv' n a a' h).symm x + (opEquiv' n a a' h).symm y := by
  dsimp [opEquiv']
  erw [opEquiv_symm_add, Iso.homToEquiv_apply, Iso.homToEquiv_apply, Iso.homToEquiv_apply]
  rw [Preadditive.add_comp]
  rfl

end Preadditive

end ShiftedHom

end CategoryTheory
