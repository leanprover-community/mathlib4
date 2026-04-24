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
      -- these two should be separate lemmas
      map_mul' x y := ((yonedaMonObj R).map f).hom.map_mul x y
      map_add' x y := ((yonedaAddMonObj R).map f).hom.map_add x y }

@[simp]
lemma yonedaRingObj_map_apply {R : C} [RingObj R] {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : X.unop ⟶ R) :
    dsimp% (yonedaRingObj R).map f x = f.unop ≫ x := rfl

/-- The yoneda embedding of `RingObjCat C` into presheaves of rings. -/
def yonedaRing : RingObjCat C ⥤ Cᵒᵖ ⥤ RingCat.{v} where
  obj R := yonedaRingObj R.X
  map f :=
    { app X := RingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' x y :=
            ((yonedaMon.map ((RingObjCat.forget₂Mon C).map f)).app X).hom.map_mul x y
          map_add' x y :=
            ((yonedaAddMon.map ((RingObjCat.forget₂AddMon C).map f)).app X).hom.map_add x y }
      naturality _ _ f := by ext g; apply Category.assoc }
  map_comp _ _ := by ext; exact (Category.assoc ..).symm

/-- If `R` is a commutative ring object, then `Hom(-, R)` is a presheaf of commutative rings. -/
@[simps! obj]
def yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

/-- The yoneda embedding of `CommRingObjCat C` into presheaves of commutative rings. -/
def yonedaCommRing : CommRingObjCat C ⥤ Cᵒᵖ ⥤ CommRingCat.{v} where
  obj R := yonedaCommRingObj R.X
  map f :=
    { app X := CommRingCat.ofHom
        { toFun x := x ≫ f.hom
          map_one' := by simp
          map_zero' := by simp
          map_mul' x y :=
            ((yonedaMon.map ((CommRingObjCat.forget₂RingObjCat C ⋙
              RingObjCat.forget₂Mon C).map f)).app X).hom.map_mul x y
          map_add' x y :=
            ((yonedaAddMon.map ((CommRingObjCat.forget₂RingObjCat C ⋙
              RingObjCat.forget₂AddMon C).map f)).app X).hom.map_add x y }
      naturality _ _ f := by ext; apply Category.assoc }
  map_comp _ _ := by ext; exact (Category.assoc ..).symm

end CategoryTheory
