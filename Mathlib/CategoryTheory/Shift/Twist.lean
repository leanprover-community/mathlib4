/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Shift.Basic

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

end TwistShift

end CategoryTheory
