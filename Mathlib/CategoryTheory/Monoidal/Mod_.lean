/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

#align_import category_theory.monoidal.Mod_ from "leanprover-community/mathlib"@"33085c9739c41428651ac461a323fde9a2688d9b"

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {C}

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod_ (A : Mon_ C) where
  X : C
  act : A.X ⊗ X ⟶ X
  one_act : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).hom := by aesop_cat
  assoc : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act) ≫ act := by aesop_cat
set_option linter.uppercaseLean3 false in
#align Mod_ Mod_

attribute [reassoc (attr := simp)] Mod_.one_act Mod_.assoc

namespace Mod_

variable {A : Mon_ C} (M : Mod_ A)

theorem assoc_flip :
    (𝟙 A.X ⊗ M.act) ≫ M.act = (α_ A.X A.X M.X).inv ≫ (A.mul ⊗ 𝟙 M.X) ≫ M.act := by simp
                                                                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Mod_.assoc_flip Mod_.assoc_flip

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of module objects. -/
@[ext]
structure Hom (M N : Mod_ A) where
  hom : M.X ⟶ N.X
  act_hom : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act := by aesop_cat
set_option linter.uppercaseLean3 false in
#align Mod_.hom Mod_.Hom

attribute [reassoc (attr := simp)] Hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod_ A) : Hom M M where hom := 𝟙 M.X
set_option linter.uppercaseLean3 false in
#align Mod_.id Mod_.id

instance homInhabited (M : Mod_ A) : Inhabited (Hom M M) :=
  ⟨id M⟩
set_option linter.uppercaseLean3 false in
#align Mod_.hom_inhabited Mod_.homInhabited

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod_ A} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom
set_option linter.uppercaseLean3 false in
#align Mod_.comp Mod_.comp

instance : Category (Mod_ A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

-- porting note: added because `Hom.ext` is not triggered automatically
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma hom_ext {M N : Mod_ A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂ :=
  Hom.ext _ _ h

@[simp]
theorem id_hom' (M : Mod_ A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Mod_.id_hom' Mod_.id_hom'

@[simp]
theorem comp_hom' {M N K : Mod_ A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Mod_.comp_hom' Mod_.comp_hom'

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ A where
  X := A.X
  act := A.mul
set_option linter.uppercaseLean3 false in
#align Mod_.regular Mod_.regular

instance : Inhabited (Mod_ A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Mod_ A ⥤ C where
  obj A := A.X
  map f := f.hom
set_option linter.uppercaseLean3 false in
#align Mod_.forget Mod_.forget

open CategoryTheory.MonoidalCategory

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod_ B ⥤ Mod_ A where
  obj M :=
    { X := M.X
      act := (f.hom ⊗ 𝟙 M.X) ≫ M.act
      one_act := by
        slice_lhs 1 2 => rw [← comp_tensor_id]
        -- ⊢ (A.one ≫ f.hom ⊗ 𝟙 M.X) ≫ M.act = (λ_ M.X).hom
        rw [f.one_hom, one_act]
        -- 🎉 no goals
      assoc := by
        -- oh, for homotopy.io in a widget!
        slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (α_ A.X A.X M.X).hom ≫ ((f.hom ⊗ …
        rw [id_tensor_comp]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (α_ A.X A.X M.X).hom ≫ ((f.hom ⊗ …
        slice_rhs 4 5 => rw [Mod_.assoc_flip]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (α_ A.X A.X M.X).hom ≫ (f.hom ⊗  …
        slice_rhs 3 4 => rw [associator_inv_naturality]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (α_ A.X A.X M.X).hom ≫ (f.hom ⊗  …
        slice_rhs 2 3 => rw [← tensor_id, associator_inv_naturality]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (α_ A.X A.X M.X).hom ≫ ((((α_ A. …
        slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = ((((f.hom ⊗ 𝟙 A.X) ⊗ 𝟙 M.X) ≫ (( …
        slice_rhs 1 2 => rw [← comp_tensor_id, tensor_id_comp_id_tensor]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (((f.hom ⊗ f.hom) ⊗ 𝟙 M.X) ≫ (B. …
        slice_rhs 1 2 => rw [← comp_tensor_id, ← f.mul_hom]
        -- ⊢ (A.mul ⊗ 𝟙 M.X) ≫ (f.hom ⊗ 𝟙 M.X) ≫ M.act = (A.mul ≫ f.hom ⊗ 𝟙 M.X) ≫ M.act
        rw [comp_tensor_id, Category.assoc] }
        -- 🎉 no goals
  map g :=
    { hom := g.hom
      act_hom := by
        dsimp
        -- ⊢ ((f.hom ⊗ 𝟙 X✝.X) ≫ X✝.act) ≫ g.hom = (𝟙 A.X ⊗ g.hom) ≫ (f.hom ⊗ 𝟙 Y✝.X) ≫ Y …
        slice_rhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        -- ⊢ ((f.hom ⊗ 𝟙 X✝.X) ≫ X✝.act) ≫ g.hom = ((f.hom ⊗ 𝟙 X✝.X) ≫ (𝟙 B.X ⊗ g.hom)) ≫ …
        slice_rhs 2 3 => rw [← g.act_hom]
        -- ⊢ ((f.hom ⊗ 𝟙 X✝.X) ≫ X✝.act) ≫ g.hom = (f.hom ⊗ 𝟙 X✝.X) ≫ X✝.act ≫ g.hom
        rw [Category.assoc] }
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Mod_.comap Mod_.comap

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end Mod_
