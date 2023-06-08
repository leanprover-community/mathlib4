/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.Mod_
! leanprover-community/mathlib commit 33085c9739c41428651ac461a323fde9a2688d9b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod_ (A : Mon_ C) where
  pt : C
  act : A.pt ⊗ X ⟶ X
  one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).Hom := by obviously
  assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.pt A.pt X).Hom ≫ (𝟙 A.pt ⊗ act) ≫ act := by obviously
#align Mod_ Mod_

restate_axiom Mod_.one_act'

restate_axiom Mod_.assoc'

attribute [simp, reassoc] Mod_.one_act Mod_.assoc

namespace Mod_

variable {A : Mon_ C} (M : Mod_ A)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem assoc_flip :
    (𝟙 A.pt ⊗ M.act) ≫ M.act = (α_ A.pt A.pt M.pt).inv ≫ (A.mul ⊗ 𝟙 M.pt) ≫ M.act := by simp
#align Mod_.assoc_flip Mod_.assoc_flip

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of module objects. -/
@[ext]
structure Hom (M N : Mod_ A) where
  Hom : M.pt ⟶ N.pt
  act_hom' : M.act ≫ hom = (𝟙 A.pt ⊗ hom) ≫ N.act := by obviously
#align Mod_.hom Mod_.Hom

restate_axiom hom.act_hom'

attribute [simp, reassoc] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod_ A) : Hom M M where Hom := 𝟙 M.pt
#align Mod_.id Mod_.id

instance homInhabited (M : Mod_ A) : Inhabited (Hom M M) :=
  ⟨id M⟩
#align Mod_.hom_inhabited Mod_.homInhabited

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod_ A} (f : Hom M N) (g : Hom N O) : Hom M O where Hom := f.Hom ≫ g.Hom
#align Mod_.comp Mod_.comp

instance : Category (Mod_ A) where
  Hom M N := Hom M N
  id := id
  comp M N O f g := comp f g

@[simp]
theorem id_hom' (M : Mod_ A) : (𝟙 M : Hom M M).Hom = 𝟙 M.pt :=
  rfl
#align Mod_.id_hom' Mod_.id_hom'

@[simp]
theorem comp_hom' {M N K : Mod_ A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Mod_.comp_hom' Mod_.comp_hom'

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ A where
  pt := A.pt
  act := A.mul
#align Mod_.regular Mod_.regular

instance : Inhabited (Mod_ A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Mod_ A ⥤ C where
  obj A := A.pt
  map A B f := f.Hom
#align Mod_.forget Mod_.forget

open CategoryTheory.MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod_ B ⥤ Mod_ A where
  obj M :=
    { pt := M.pt
      act := (f.Hom ⊗ 𝟙 M.pt) ≫ M.act
      one_act' := by
        slice_lhs 1 2 => rw [← comp_tensor_id]
        rw [f.one_hom, one_act]
      assoc' := by
        -- oh, for homotopy.io in a widget!
        slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        rw [id_tensor_comp]
        slice_rhs 4 5 => rw [Mod_.assoc_flip]
        slice_rhs 3 4 => rw [associator_inv_naturality]
        slice_rhs 2 3 => rw [← tensor_id, associator_inv_naturality]
        slice_rhs 1 3 => rw [iso.hom_inv_id_assoc]
        slice_rhs 1 2 => rw [← comp_tensor_id, tensor_id_comp_id_tensor]
        slice_rhs 1 2 => rw [← comp_tensor_id, ← f.mul_hom]
        rw [comp_tensor_id, category.assoc] }
  map M N g :=
    { Hom := g.Hom
      act_hom' := by
        dsimp
        slice_rhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        slice_rhs 2 3 => rw [← g.act_hom]
        rw [category.assoc] }
#align Mod_.comap Mod_.comap

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end Mod_

