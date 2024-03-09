/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

#align_import algebra.category.Module.monoidal.symmetric from "leanprover-community/mathlib"@"74403a3b2551b0970855e14ef5e8fd0d6af1bfc2"

/-!
# The symmetric monoidal structure on `Module R`.
-/

suppress_compilation

universe v w x u

open CategoryTheory MonoidalCategory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- (implementation) the braiding for R-modules -/
def braiding (M N : ModuleCat.{u} R) : M ⊗ N ≅ N ⊗ M :=
  LinearEquiv.toModuleIso (TensorProduct.comm R M N)
set_option linter.uppercaseLean3 false in
#align Module.braiding ModuleCat.braiding

namespace MonoidalCategory

@[simp]
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : ModuleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g ⊗ f) := by
  apply TensorProduct.ext'
  intro x y
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.braiding_naturality ModuleCat.MonoidalCategory.braiding_naturality

@[simp]
theorem braiding_naturality_left {X Y : ModuleCat R} (f : X ⟶ Y) (Z : ModuleCat R) :
    f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
theorem braiding_naturality_right (X : ModuleCat R) {Y Z : ModuleCat R} (f : Y ⟶ Z) :
    X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  simp_rw [← id_tensorHom]
  apply braiding_naturality

@[simp]
theorem hexagon_forward (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).hom ≫ (braiding X _).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (braiding X Z).hom := by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.hexagon_forward ModuleCat.MonoidalCategory.hexagon_forward

@[simp]
theorem hexagon_reverse (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply (cancel_epi (α_ X Y Z).hom).1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.hexagon_reverse ModuleCat.MonoidalCategory.hexagon_reverse

attribute [local ext] TensorProduct.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R) where
  braiding := braiding
  braiding_naturality_left := braiding_naturality_left
  braiding_naturality_right := braiding_naturality_right
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  -- Porting note: this proof was automatic in Lean3
  -- now `aesop` is applying `ModuleCat.ext` in favour of `TensorProduct.ext`.
  symmetry _ _ := by
    apply TensorProduct.ext'
    aesop_cat
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.symmetric_category ModuleCat.MonoidalCategory.symmetricCategory

@[simp]
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.braiding_hom_apply ModuleCat.MonoidalCategory.braiding_hom_apply

@[simp]
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.monoidal_category.braiding_inv_apply ModuleCat.MonoidalCategory.braiding_inv_apply

end MonoidalCategory

end ModuleCat
