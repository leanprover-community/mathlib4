/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Yoneda embedding of `RingCatObj C`

-/

@[expose] public section

open CategoryTheory MonObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

open scoped CommRingObj RingObj

/-- If `R` is a ring object, then `Hom(-, R)` is a presheaf of rings. -/
@[simps! obj]
def yonedaRingObj (R : C) [RingObj R] : Cᵒᵖ ⥤ RingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := RingCat.ofHom
    { toFun x := f.unop ≫ x
      map_one' := by simp
      map_zero' := by simp
      map_mul' _ _ := MonObj.comp_mul _ _ _
      map_add' _ _ := AddMonObj.comp_add _ _ _ }

@[simp]
lemma yonedaRingObj_map_apply {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `RingObjCat C` into presheaves of rings. -/
def yonedaRing : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where
  obj R := yonedaRingObj R.X
  map f :=
    { app X := RingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

/-- If `R` is a commutative ring object, then `Hom(-, R)` is a presheaf of commutative rings. -/
@[simps obj]
def yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

@[simp]
lemma yonedaCommRingObj_map_apply {R : C} [CommRingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaCommRingObj R).map f x = f.unop ≫ x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `CommRingObjCat C` into presheaves of commutative rings. -/
@[simps obj]
def yonedaCommRing : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where
  obj R := yonedaCommRingObj R.X
  map f :=
    { app X := CommRingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' _ _ := MonObj.mul_comp _ _ _
          map_add' _ _ := AddMonObj.add_comp _ _ _ } }

@[simp]
lemma yonedaCommRing_map_app_apply {R₁ R₂ : CommRingObjCat C} (f : R₁ ⟶ R₂)
    {X : C} (x : X ⟶ R₁.X) :
    dsimp% (yonedaCommRing.map f).app _ x = x ≫ f.hom := rfl

end CategoryTheory
