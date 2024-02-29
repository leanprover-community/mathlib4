/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Coherence

#align_import category_theory.monoidal.coherence_lemmas from "leanprover-community/mathlib"@"b8b8bf3ea0c625fa1f950034a184e07c67f7bcfe"

/-!
# Lemmas which are consequences of monoidal coherence

These lemmas are all proved `by coherence`.

## Future work
Investigate whether these lemmas are really needed,
or if they can be replaced by use of the `coherence` tactic.
-/


open CategoryTheory Category Iso

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
theorem leftUnitor_tensor'' (X Y : C) :
    (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ⊗ 𝟙 Y := by
  coherence
#align category_theory.monoidal_category.left_unitor_tensor' CategoryTheory.MonoidalCategory.leftUnitor_tensor''

@[reassoc]
theorem leftUnitor_tensor' (X Y : C) :
    (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ ((λ_ X).hom ⊗ 𝟙 Y) := by
  coherence
#align category_theory.monoidal_category.left_unitor_tensor CategoryTheory.MonoidalCategory.leftUnitor_tensor'

@[reassoc]
theorem leftUnitor_tensor_inv' (X Y : C) :
    (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).hom := by coherence
#align category_theory.monoidal_category.left_unitor_tensor_inv CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv'

@[reassoc]
theorem id_tensor_rightUnitor_inv (X Y : C) : 𝟙 X ⊗ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  coherence
#align category_theory.monoidal_category.id_tensor_right_unitor_inv CategoryTheory.MonoidalCategory.id_tensor_rightUnitor_inv

@[reassoc]
theorem leftUnitor_inv_tensor_id (X Y : C) : (λ_ X).inv ⊗ 𝟙 Y = (λ_ _).inv ≫ (α_ _ _ _).inv := by
  coherence
#align category_theory.monoidal_category.left_unitor_inv_tensor_id CategoryTheory.MonoidalCategory.leftUnitor_inv_tensor_id

@[reassoc]
theorem pentagon_inv_inv_hom (W X Y Z : C) :
    (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) ≫ (α_ (W ⊗ X) Y Z).hom =
      (𝟙 W ⊗ (α_ X Y Z).hom) ≫ (α_ W X (Y ⊗ Z)).inv := by
  coherence
#align category_theory.monoidal_category.pentagon_inv_inv_hom CategoryTheory.MonoidalCategory.pentagon_inv_inv_hom

theorem unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  coherence
#align category_theory.monoidal_category.unitors_equal CategoryTheory.MonoidalCategory.unitors_equal

theorem unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  coherence
#align category_theory.monoidal_category.unitors_inv_equal CategoryTheory.MonoidalCategory.unitors_inv_equal

@[reassoc]
theorem pentagon_hom_inv {W X Y Z : C} :
    (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) =
      (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom := by
  coherence
#align category_theory.monoidal_category.pentagon_hom_inv CategoryTheory.MonoidalCategory.pentagon_hom_inv

@[reassoc]
theorem pentagon_inv_hom (W X Y Z : C) :
    (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv := by
  coherence
#align category_theory.monoidal_category.pentagon_inv_hom CategoryTheory.MonoidalCategory.pentagon_inv_hom

end CategoryTheory.MonoidalCategory
