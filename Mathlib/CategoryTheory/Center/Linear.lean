/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Center.Preadditive

/-!
# Center of a linear category

If `C` is an `R`-linear category, we define a ring morphism `R →+* CatCenter C`
and conversely, if `C` is a preadditive category, and `φ : R →+* CatCenter C`
is a ring morphism, we define an `R`-linear structure on `C` attached to `φ`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits

namespace Linear

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
/-- The canonical morphism `R →+* CatCenter C` when `C` is an `R`-linear category. -/
@[simps]
def toCatCenter [Linear R C] : R →+* CatCenter C where
  toFun a := .of { app := fun X => a • 𝟙 X }
  map_one' := by cat_disch
  map_mul' a b := by
    rw [mul_comm]
    ext X
    dsimp only [CatCenter.mul_app']
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
    simp
  map_zero' := by cat_disch
  map_add' a b := by ext X; simp [add_smul]

section

variable {R C}
variable (φ : R →+* CatCenter C) (X Y : C)

/-- The scalar multiplication by `R` on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
def smulOfRingMorphism : SMul R (X ⟶ Y) where
  smul a f := (φ a).app X ≫ f

variable {X Y}

lemma smulOfRingMorphism_smul_eq (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

/-- `a • f = f ≫ (φ a).app Y`. -/
lemma smulOfRingMorphism_smul_eq' (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

variable (X Y)

/-- The `R`-module structure on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
def homModuleOfRingMorphism : Module R (X ⟶ Y) := by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul _ := by simp [smulOfRingMorphism_smul_eq]
    mul_smul _ _ _ := by simp [smulOfRingMorphism_smul_eq, CatCenter.mul_app]
    smul_zero _ := by simp only [smulOfRingMorphism_smul_eq, comp_zero]
    zero_smul _ := by simp [smulOfRingMorphism_smul_eq]
    smul_add _ _ := by simp [smulOfRingMorphism_smul_eq]
    add_smul _ _ _ := by simp [smulOfRingMorphism_smul_eq] }

/-- The `R`-linear structure on a preadditive category `C` equipped with
a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
def ofRingMorphism : Linear R C := by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

end

end Linear

end CategoryTheory
