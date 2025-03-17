/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! Shifted morphisms in the opposite category

If `C` is a category equipped with a shift by `ℤ`, `X` and `Y` are objects
of `C`, and `n : ℤ`, we define a bijection
`ShiftedHom.opEquiv : ShiftedHom X Y n ≃ ShiftedHom (Opposite.op Y) (Opposite.op X) n`.
We also introduce `ShiftedHom.opEquiv'` which produces a bijection
`ShiftedHom X Y a' ≃ (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦n⟧)` when `n + a = a'`.
The compatibilities that are obtained shall be used in order to study
the homological functor `preadditiveYoneda.obj B : Cᵒᵖ ⥤ Type _` when `B` is an object
in a pretriangulated category `C`.

-/

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

lemma opEquiv_symm_apply_comp {X Y : C} {a : ℤ}
    (f : ShiftedHom (Opposite.op X) (Opposite.op Y) a) {b : ℤ} {Z : C}
    (z : ShiftedHom X Z b) {c : ℤ} (h : b + a = c) :
    ((ShiftedHom.opEquiv a).symm f).comp z h =
      (ShiftedHom.opEquiv a).symm (z.op ≫ f) ≫
        (shiftFunctorAdd' C b a c h).inv.app Z := by
  rw [ShiftedHom.opEquiv_symm_apply, ShiftedHom.opEquiv_symm_apply,
    ShiftedHom.comp]
  dsimp
  simp only [assoc, Functor.map_comp]

lemma opEquiv_symm_comp {a b : ℤ}
    (f : ShiftedHom (Opposite.op Z) (Opposite.op Y) a)
    (g : ShiftedHom (Opposite.op Y) (Opposite.op X) b)
    {c : ℤ} (h : b + a = c) :
    (opEquiv _).symm (f.comp g h) =
      ((opEquiv _).symm g).comp ((opEquiv _).symm f) (by omega) := by
  rw [opEquiv_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_unitIso_inv_app_eq _ _ _ _ (show a + b = c by omega), comp, comp]
  dsimp
  rw [assoc, assoc, assoc, assoc, ← Functor.map_comp, ← unop_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp
  rw [assoc, id_comp, Functor.map_comp, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality, opEquiv_symm_apply]
  dsimp
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  rw [← unop_comp_assoc]
  erw [← NatTrans.naturality]
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

lemma opEquiv'_apply {a' : ℤ} (f : ShiftedHom X Y a') (n a : ℤ) (h : n + a = a') :
    opEquiv' n a a' h f =
      opEquiv n (f ≫ (shiftFunctorAdd' C a n a' (by omega)).hom.app Y) := by
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

lemma opEquiv'_symm_comp (f : Y ⟶ X) {n a : ℤ} (x : Opposite.op (Z⟦a⟧) ⟶ (Opposite.op X⟦n⟧))
    (a' : ℤ) (h : n + a = a') :
    (opEquiv' n a a' h).symm (x ≫ f.op⟦n⟧') = f ≫ (opEquiv' n a a' h).symm x :=
  Quiver.Hom.op_inj (by simp [opEquiv'_symm_apply, opEquiv_symm_apply])

lemma opEquiv'_zero_add_symm (a : ℤ) (f : Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦(0 : ℤ)⟧) :
    (opEquiv' 0 a a (zero_add a)).symm f =
      ((shiftFunctorZero Cᵒᵖ ℤ).hom.app _).unop ≫ f.unop := by
  simp [opEquiv'_symm_apply, opEquiv_symm_apply, shiftFunctorAdd'_add_zero,
    opShiftFunctorEquivalence_zero_unitIso_inv_app]

lemma opEquiv'_add_symm (n m a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (x : (Opposite.op (Y⟦a⟧) ⟶ (Opposite.op X)⟦m + n⟧)) :
    (opEquiv' (m + n) a a'' (by omega)).symm x =
      (opEquiv' m a' a'' ha'').symm ((opEquiv' n a a' ha').symm
        (x ≫ (shiftFunctorAdd Cᵒᵖ m n).hom.app _)).op := by
  simp only [opEquiv'_symm_apply, opEquiv_symm_apply,
    opShiftFunctorEquivalence_unitIso_inv_app_eq _ _ _ _ (add_comm n m)]
  dsimp
  simp only [assoc, Functor.map_comp, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
    ← NatTrans.naturality_assoc,
    shiftFunctorAdd'_assoc_inv_app a n m a' (m + n) a'' (by omega) (by omega) (by omega)]
  rfl

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
