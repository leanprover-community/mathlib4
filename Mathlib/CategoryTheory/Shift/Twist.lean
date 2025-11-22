/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Twisting a shift

Given a category `C` equipped with a shift by a monoid `A`, we introduce a structure
`t : TwistShiftData C A` which consists of a collection of invertible elements in the
center of the category `C` (typically, this will be suitable signs when we
assume `C` is preadditive), which allow to introduce a type synonym
category `TwistShift t` which identical shift functors as `C` but where
the isomorphisms `shiftFunctorAdd` have been modified.

-/

@[expose] public section

namespace CategoryTheory

variable (C : Type*) [Category C] (A : Type*) [AddMonoid A] [HasShift C A]

/-- Given a category `C` equipped with a shift by a monoid `A` -/
structure TwistShiftData where
  /-- The invertible elements in the center of `C` which are used to
  modify the `shiftFunctorAdd` isomorphisms . -/
  z (a b : A) : (CatCenter C)ˣ
  z_zero_right (a : A) : z a 0 = 1 := by cat_disch
  z_zero_left (b : A) : z 0 b = 1 := by cat_disch
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c := by cat_disch
  commShift (a b : A) : NatTrans.CommShift (z a b).1 A := by infer_instance

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [simp] z_zero_right z_zero_left
attribute [instance] commShift

@[simp]
lemma shift_z_app (a b c : A) (X : C) :
    ((t.z a b).1.app X)⟦c⟧' = (t.z a b).1.app (X⟦c⟧) := by
  simpa using NatTrans.shift_app_comm (t.z a b).1 c X

end TwistShiftData

variable {C A}

/-- Given `t : TwistShiftData C A`, this is a type synonym for the category `C`,
which the same shift functors as `C` but where the `shiftFunctorAdd` isomorphisms
have been modified using `t`. -/
@[nolint unusedArguments]
def TwistShift (_ : TwistShiftData C A) : Type _ := C

variable (t : TwistShiftData C A)

namespace TwistShift

instance : Category (TwistShift t) := inferInstanceAs (Category C)

/-- Given `t : TwistShiftData C A`, the shift on the category `TwistShift t` has
the same shift functors as `C`, the same isomorphism `shiftFunctorZero` isomorphism,
but the `shiftFunctorAdd` isomorphisms are modified using `t`. -/
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
lemma shiftFunctor_obj (X : TwistShift t) (a : A) :
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
  dsimp [shiftFunctorAdd']
  cat_disch

@[simp]
lemma shiftFunctorAdd'_inv_app (i j k : A) (h : i + j = k) (X : TwistShift t) :
    (shiftFunctorAdd' (TwistShift t) i j k h).inv.app X =
      ((t.z i j)⁻¹).1 • (shiftFunctorAdd' C i j k h).inv.app X := by
  dsimp [shiftFunctorAdd']
  cat_disch

end TwistShift

end CategoryTheory
