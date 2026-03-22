/-
Copyright (c) 2026 Joël Riou, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Yoneda embedding of `Ring C`

-/

@[expose] public section

open CategoryTheory MonObj

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

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

/-- If `R` is a commutative ring object, then `Hom(-, R)` is a presheaf of commutative rings. -/
@[simps! obj]
def yonedaCommRingObj (R : C) [CommRingObj R] : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)
  map f := CommRingCat.ofHom ((yonedaRingObj R).map f).hom

end CategoryTheory
