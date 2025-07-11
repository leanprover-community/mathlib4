/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Shift.Basic

/-!
# Twisting a shift

-/

namespace CategoryTheory

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [HasShift C A]

structure TwistShiftData where
  z (a b : A) : (CatCenter C)ˣ
  z_zero_right (a : A) : z a 0 = 1
  z_zero_left (b : A) : z 0 b = 1
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c
  shift_z_app (a b c : A) (X : C) : ((z a b).1.app X)⟦c⟧' = (z a b).1.app (X⟦c⟧)

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [simp] z_zero_right z_zero_left shift_z_app

end TwistShiftData

variable {C A}
@[nolint unusedArguments]
def TwistShift (_ : TwistShiftData C A) : Type _ := C

variable (t : TwistShiftData C A)

namespace TwistShift

instance : Category (TwistShift t) := inferInstanceAs (Category C)

def shiftMkCore : ShiftMkCore (TwistShift t) A where
  F a := shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X ↦ t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc]
    rw [CatCenter.naturality, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      CatCenter.naturality_assoc, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      t.shift_z_app, CatCenter.naturality, CatCenter.naturality_assoc,
      ← CatCenter.mul_app_assoc, ← CatCenter.mul_app_assoc,
      ← Units.val_mul, ← Units.val_mul, t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']

instance : HasShift (TwistShift t) A := hasShiftMk _ _ (shiftMkCore t)

@[simp]
lemma shiftFunctor_obj (X : TwistShift t) (a : A):
    (shiftFunctor (TwistShift t) a).obj X = (shiftFunctor C a).obj X := rfl

@[simp]
lemma shiftFunctorZero_hom_app (X : TwistShift t) :
    (shiftFunctorZero (TwistShift t) A).hom.app X = (shiftFunctorZero C A).hom.app X := rfl

@[simp]
lemma shiftFunctorZero_inv_app (X : TwistShift t) :
    (shiftFunctorZero (TwistShift t) A).inv.app X = (shiftFunctorZero C A).inv.app X := rfl

@[simp]
lemma shiftFunctorAdd'_hom_app (i j k : A) (h : i + j = k) (X : TwistShift t) :
    (shiftFunctorAdd' (TwistShift t) i j k h).hom.app X =
      (t.z i j).1 • (shiftFunctorAdd' C i j k h).hom.app X := by
  subst h
  simp only [Functor.comp_obj, shiftFunctorAdd', eqToIso_refl, Iso.refl_trans,
    CatCenter.smul_eq, Functor.id_obj]
  rfl

@[simp]
lemma shiftFunctorAdd'_inv_app (i j k : A) (h : i + j = k) (X : TwistShift t) :
    (shiftFunctorAdd' (TwistShift t) i j k h).inv.app X =
      ((t.z i j)⁻¹).1 • (shiftFunctorAdd' C i j k h).inv.app X := by
  subst h
  simp only [Functor.comp_obj, shiftFunctorAdd', eqToIso_refl, Iso.refl_trans,
    CatCenter.smul_eq, Functor.id_obj]
  rfl

end TwistShift

end CategoryTheory
