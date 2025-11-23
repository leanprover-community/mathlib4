/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Twisting a shift

Given a category `C` equipped with a shift by a monoid `A`, we introduce a structure
`t : TwistShiftData C A` which consists of a collection of invertible elements in the
center of the category `C` (typically, this will be suitable signs when we
assume `C` is preadditive), which allow to introduce a type synonym
category `TwistShift t` which identical shift functors as `C` but where
the isomorphisms `shiftFunctorAdd` have been modified.

-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (A : Type w) [AddMonoid A] [HasShift C A]

/-- Given a category `C` equipped with a shift by a monoid `A` -/
structure TwistShiftData where
  /-- The invertible elements in the center of `C` which are used to
  modify the `shiftFunctorAdd` isomorphisms . -/
  z (a b : A) : (CatCenter C)ˣ
  z_zero_right (a : A) : z a 0 = 1 := by aesop_cat
  z_zero_left (b : A) : z 0 b = 1 := by aesop_cat
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c := by aesop_cat
  commShift (a b : A) : NatTrans.CommShift (z a b).val A := by infer_instance

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [simp] z_zero_right z_zero_left
attribute [instance] commShift

@[simp]
lemma shift_z_app (a b c : A) (X : C) :
    ((t.z a b).val.app X)⟦c⟧' = (t.z a b).val.app (X⟦c⟧) := by
  simpa using NatTrans.shift_app_comm (t.z a b).val c X

/-- Given `t : TwistShiftData C A`, this is a type synonym for the category `C`,
which the same shift functors as `C` but where the `shiftFunctorAdd` isomorphisms
have been modified using `t`. -/
@[nolint unusedArguments]
protected def Category (_ : TwistShiftData C A) : Type u := C

instance : Category t.Category := inferInstanceAs (Category C)

/-- Given `t : TwistShiftData C A`, the shift on the category `TwistShift t` has
the same shift functors as `C`, the same isomorphism `shiftFunctorZero` isomorphism,
but the `shiftFunctorAdd` isomorphisms are modified using `t`. -/
def shiftMkCore : ShiftMkCore t.Category A where
  F a := shiftFunctor C a
  zero := shiftFunctorZero C A
  add a b := NatIso.ofComponents (fun X ↦ t.z a b • (shiftFunctorAdd C a b).app X) (by
    simp [CatCenter.naturality_assoc, CatCenter.naturality, CatCenter.smul_iso_hom_eq])
  add_zero_hom_app := by simp [shiftFunctorAdd_add_zero_hom_app, CatCenter.smul_iso_hom_eq]
  zero_add_hom_app := by simp [shiftFunctorAdd_zero_add_hom_app, CatCenter.smul_iso_hom_eq]
  assoc_hom_app a b c X := by
    dsimp
    simp only [Functor.map_comp, Category.assoc, CatCenter.smul_iso_hom_eq]
    rw [CatCenter.naturality, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      CatCenter.naturality_assoc, CatCenter.naturality_assoc, CatCenter.naturality_assoc,
      t.shift_z_app, CatCenter.naturality, CatCenter.naturality_assoc,
      ← CatCenter.mul_app_assoc, ← CatCenter.mul_app_assoc,
      ← Units.val_mul, ← Units.val_mul, t.assoc a b c]
    simp [shiftFunctorAdd_assoc_hom_app (C := C) a b c X, shiftFunctorAdd']

instance hasShift : HasShift t.Category A := hasShiftMk _ _ (shiftMkCore t)

noncomputable def shiftIso (m : A) : shiftFunctor t.Category m ≅ shiftFunctor C m :=
  Iso.refl _

lemma shiftFunctor_map {X Y : t.Category} (f : X ⟶ Y) (m : A) :
    (shiftFunctor t.Category m).map f =
      (t.shiftIso m).hom.app X ≫ (shiftFunctor C m).map f ≫ (t.shiftIso m).inv.app Y := by
  simp

lemma shiftFunctorZero_hom_app (X : t.Category) :
    (shiftFunctorZero t.Category A).hom.app X =
      (shiftIso t (0 : A)).hom.app X ≫ (shiftFunctorZero C A).hom.app X :=
  (Category.id_comp _).symm

lemma shiftFunctorZero_inv_app (X : t.Category) :
    (shiftFunctorZero t.Category A).inv.app X =
      (shiftFunctorZero C A).inv.app X ≫ (shiftIso t (0 : A)).inv.app X :=
  (Category.comp_id _).symm

@[simp]
lemma shiftFunctorAdd'_hom_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (t.shiftIso k).hom.app X ≫
        (shiftFunctorAdd' C i j k h).hom.app X ≫
        (shiftFunctor C j).map ((t.shiftIso i).inv.app X) ≫ (t.shiftIso j).inv.app _ := by
  have : (shiftFunctorAdd' t.Category i j k h).hom.app X =
      (t.z i j).val • (shiftFunctorAdd' C i j k h).hom.app X := by
    dsimp [shiftFunctorAdd']
    aesop
  rw [this]
  congr
  change _ = 𝟙 _ ≫ _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ 𝟙 _
  simp

@[simp]
lemma shiftFunctorAdd'_inv_app (i j k : A) (h : i + j = k) (X : t.Category) :
    (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (t.shiftIso j).hom.app _  ≫
        (shiftFunctor C j).map ((t.shiftIso i).hom.app X) ≫
        (shiftFunctorAdd' C i j k h).inv.app X ≫
        (t.shiftIso k).inv.app X := by
  have : (shiftFunctorAdd' t.Category i j k h).inv.app X =
      ((t.z i j)⁻¹).val • (shiftFunctorAdd' C i j k h).inv.app X := by
    dsimp [shiftFunctorAdd']
    aesop
  rw [this]
  congr
  change _ = 𝟙 _ ≫ (shiftFunctor C j).map (𝟙 _) ≫ _ ≫ 𝟙 _
  simp

end TwistShiftData

end CategoryTheory
