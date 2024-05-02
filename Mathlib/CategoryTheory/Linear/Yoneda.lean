/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

#align_import category_theory.linear.yoneda from "leanprover-community/mathlib"@"09f981f72d43749f1fa072deade828d9c1e185bb"

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linearYoneda R C` is `R`-linear.
TODO: In fact, `linearYoneda` itself is additive and `R`-linear.
-/


universe w v u

open Opposite

namespace CategoryTheory

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable (C)

-- Porting note: inserted specific `ModuleCat.ofHom` in the definition of `linearYoneda`
-- and similarly in `linearCoyoneda`, otherwise many simp lemmas are not triggered automatically.
-- Eventually, doing so allows more proofs to be automatic!
/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  obj X :=
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }
#align category_theory.linear_yoneda CategoryTheory.linearYoneda

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `Module R`-valued copresheaf on `C`,
with value on `X : C` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  obj Y :=
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }
#align category_theory.linear_coyoneda CategoryTheory.linearCoyoneda

instance linearYoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where
#align category_theory.linear_yoneda_obj_additive CategoryTheory.linearYoneda_obj_additive

instance linearCoyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where
#align category_theory.linear_coyoneda_obj_additive CategoryTheory.linearCoyoneda_obj_additive

@[simp]
theorem whiskering_linearYoneda :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl
#align category_theory.whiskering_linear_yoneda CategoryTheory.whiskering_linearYoneda

@[simp]
theorem whiskering_linearYoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) =
      preadditiveYoneda :=
  rfl
#align category_theory.whiskering_linear_yoneda₂ CategoryTheory.whiskering_linearYoneda₂

@[simp]
theorem whiskering_linearCoyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl
#align category_theory.whiskering_linear_coyoneda CategoryTheory.whiskering_linearCoyoneda

@[simp]
theorem whiskering_linearCoyoneda₂ :
    linearCoyoneda R C ⋙
        (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) =
      preadditiveCoyoneda :=
  rfl
#align category_theory.whiskering_linear_coyoneda₂ CategoryTheory.whiskering_linearCoyoneda₂

instance full_linearYoneda : (linearYoneda R C).Full :=
  let _ :  Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
#align category_theory.linear_yoneda_full CategoryTheory.full_linearYoneda

instance full_linearCoyoneda : (linearCoyoneda R C).Full :=
  let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
#align category_theory.linear_coyoneda_full CategoryTheory.full_linearCoyoneda

instance faithful_linearYoneda : (linearYoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)
#align category_theory.linear_yoneda_faithful CategoryTheory.faithful_linearYoneda

instance faithful_linearCoyoneda : (linearCoyoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)
#align category_theory.linear_coyoneda_faithful CategoryTheory.faithful_linearCoyoneda

end CategoryTheory
