/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer

! This file was ported from Lean 3 source module algebra.category.Module.monoidal.symmetric
! leanprover-community/mathlib commit 74403a3b2551b0970855e14ef5e8fd0d6af1bfc2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.Algebra.Category.Module.Monoidal.Basic

/-!
# The symmetric monoidal structure on `Module R`.
-/


universe v w x u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- (implementation) the braiding for R-modules -/
def braiding (M N : ModuleCat.{u} R) : M ⊗ N ≅ N ⊗ M :=
  LinearEquiv.toModuleIso (TensorProduct.comm R M N)
#align Module.braiding ModuleCat.braiding

namespace MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : ModuleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ g) ≫ (Y₁.braiding Y₂).Hom = (X₁.braiding X₂).Hom ≫ (g ⊗ f) :=
  by
  apply TensorProduct.ext'
  intro x y
  rfl
#align Module.monoidal_category.braiding_naturality ModuleCat.monoidalCategory.braiding_naturality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem hexagon_forward (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).Hom ≫ (braiding X _).Hom ≫ (α_ Y Z X).Hom =
      ((braiding X Y).Hom ⊗ 𝟙 Z) ≫ (α_ Y X Z).Hom ≫ (𝟙 Y ⊗ (braiding X Z).Hom) :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
#align Module.monoidal_category.hexagon_forward ModuleCat.monoidalCategory.hexagon_forward

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem hexagon_reverse (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).Hom ≫ (α_ Z X Y).inv =
      (𝟙 X ⊗ (Y.braiding Z).Hom) ≫ (α_ X Z Y).inv ≫ ((X.braiding Z).Hom ⊗ 𝟙 Y) :=
  by
  apply (cancel_epi (α_ X Y Z).Hom).1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl
#align Module.monoidal_category.hexagon_reverse ModuleCat.monoidalCategory.hexagon_reverse

attribute [local ext] TensorProduct.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R)
    where
  braiding := braiding
  braiding_naturality' X₁ X₂ Y₁ Y₂ f g := braiding_naturality f g
  hexagon_forward' := hexagon_forward
  hexagon_reverse' := hexagon_reverse
#align Module.monoidal_category.symmetric_category ModuleCat.monoidalCategory.symmetricCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).Hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl
#align Module.monoidal_category.braiding_hom_apply ModuleCat.monoidalCategory.braiding_hom_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl
#align Module.monoidal_category.braiding_inv_apply ModuleCat.monoidalCategory.braiding_inv_apply

end MonoidalCategory

end ModuleCat

