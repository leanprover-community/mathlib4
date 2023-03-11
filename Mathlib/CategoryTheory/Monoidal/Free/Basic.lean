/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.monoidal.free.basic
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `free_monoidal_category C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `coherence.lean`.

-/


universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

section

variable (C)

/--
Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.
-/
inductive FreeMonoidalCategory : Type u
  | of : C → free_monoidal_category
  | Unit : free_monoidal_category
  | tensor : free_monoidal_category → free_monoidal_category → free_monoidal_category
  deriving Inhabited
#align category_theory.free_monoidal_category CategoryTheory.FreeMonoidalCategory

end

-- mathport name: exprF
local notation "F" => FreeMonoidalCategory

namespace FreeMonoidalCategory

/-- Formal compositions and tensor products of identities, unitors and associators. The morphisms
    of the free monoidal category are obtained as a quotient of these formal morphisms by the
    relations defining a monoidal category. -/
@[nolint has_nonempty_instance]
inductive Hom : F C → F C → Type u
  | id (X) : hom X X
  | α_hom (X Y Z : F C) : hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : hom (unit.tensor X) X
  | l_inv (X) : hom X (unit.tensor X)
  | ρ_hom (X : F C) : hom (X.tensor unit) X
  | ρ_inv (X : F C) : hom X (X.tensor unit)
  | comp {X Y Z} (f : hom X Y) (g : hom Y Z) : hom X Z
  | tensor {W X Y Z} (f : hom W Y) (g : hom X Z) : hom (W.tensor X) (Y.tensor Z)
#align category_theory.free_monoidal_category.hom CategoryTheory.FreeMonoidalCategory.Hom

-- mathport name: «expr ⟶ᵐ »
local infixr:10 " ⟶ᵐ " => Hom

/-- The morphisms of the free monoidal category satisfy 21 relations ensuring that the resulting
    category is in fact a category and that it is monoidal. -/
inductive HomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : hom_equiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : hom_equiv f g → hom_equiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : hom_equiv f g → hom_equiv g h → hom_equiv f h
  |
  comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f.comp g) (f'.comp g')
  |
  tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f.tensor g) (f'.tensor g')
  | comp_id {X Y} (f : X ⟶ᵐ Y) : hom_equiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : hom_equiv ((Hom.id _).comp f) f
  |
  assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
    hom_equiv ((f.comp g).comp h) (f.comp (g.comp h))
  | tensor_id {X Y} : hom_equiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  |
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁)
    (g₂ : Y₂ ⟶ᵐ Z₂) :
    hom_equiv ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
  | α_hom_inv {X Y Z} : hom_equiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : hom_equiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  |
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
    hom_equiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
      ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : hom_equiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : hom_equiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  |
  ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
    hom_equiv ((f.tensor (Hom.id unit)).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : hom_equiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : hom_equiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  |
  l_naturality {X Y} (f : X ⟶ᵐ Y) :
    hom_equiv (((Hom.id unit).tensor f).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  |
  pentagon {W X Y Z} :
    hom_equiv
      (((Hom.α_hom W X Y).tensor (Hom.id Z)).comp
        ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.id W).tensor (Hom.α_hom X Y Z))))
      ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  |
  triangle {X Y} :
    hom_equiv ((Hom.α_hom X unit Y).comp ((Hom.id X).tensor (Hom.l_hom Y)))
      ((Hom.ρ_hom X).tensor (Hom.id Y))
#align category_theory.free_monoidal_category.hom_equiv CategoryTheory.FreeMonoidalCategory.HomEquiv

/-- We say that two formal morphisms in the free monoidal category are equivalent if they become
    equal if we apply the relations that are true in a monoidal category. Note that we will prove
    that there is only one equivalence class -- this is the monoidal coherence theorem. -/
def setoidHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
  ⟨HomEquiv,
    ⟨fun f => HomEquiv.refl f, fun f g => HomEquiv.symm f g, fun f g h hfg hgh =>
      HomEquiv.trans hfg hgh⟩⟩
#align category_theory.free_monoidal_category.setoid_hom CategoryTheory.FreeMonoidalCategory.setoidHom

attribute [instance] setoid_hom

section

open FreeMonoidalCategory.HomEquiv

instance categoryFreeMonoidalCategory : Category.{u} (F C)
    where
  Hom X Y := Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦FreeMonoidalCategory.Hom.id _⟧
  comp X Y Z f g :=
    Quotient.map₂ Hom.comp
      (by
        intro f f' hf g g' hg
        exact comp hf hg)
      f g
  id_comp' := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id' := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc' := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)
#align category_theory.free_monoidal_category.category_free_monoidal_category CategoryTheory.FreeMonoidalCategory.categoryFreeMonoidalCategory

instance : MonoidalCategory (F C)
    where
  tensorObj X Y := FreeMonoidalCategory.tensor X Y
  tensorHom X₁ Y₁ X₂ Y₂ :=
    Quotient.map₂ Hom.tensor <| by
      intro _ _ h _ _ h'
      exact hom_equiv.tensor h h'
  tensor_id' X Y := Quotient.sound tensor_id
  tensor_comp' X₁ Y₁ Z₁ X₂ Y₂ Z₂ := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensor_comp _ _ _ _)
  tensorUnit := FreeMonoidalCategory.unit
  associator X Y Z :=
    ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv, Quotient.sound α_inv_hom⟩
  associator_naturality' X₁ X₂ X₃ Y₁ Y₂ Y₃ :=
    by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality' X Y := by
    rintro ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality' X Y := by
    rintro ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon' W X Y Z := Quotient.sound pentagon
  triangle' X Y := Quotient.sound triangle

@[simp]
theorem mk'_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl
#align category_theory.free_monoidal_category.mk_comp CategoryTheory.FreeMonoidalCategory.mk'_comp

@[simp]
theorem mk'_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl
#align category_theory.free_monoidal_category.mk_tensor CategoryTheory.FreeMonoidalCategory.mk'_tensor

@[simp]
theorem mk'_id {X : F C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl
#align category_theory.free_monoidal_category.mk_id CategoryTheory.FreeMonoidalCategory.mk'_id

@[simp]
theorem mk'_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).Hom :=
  rfl
#align category_theory.free_monoidal_category.mk_α_hom CategoryTheory.FreeMonoidalCategory.mk'_α_hom

@[simp]
theorem mk'_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_α_inv CategoryTheory.FreeMonoidalCategory.mk'_α_inv

@[simp]
theorem mk'_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).Hom :=
  rfl
#align category_theory.free_monoidal_category.mk_ρ_hom CategoryTheory.FreeMonoidalCategory.mk'_ρ_hom

@[simp]
theorem mk'_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_ρ_inv CategoryTheory.FreeMonoidalCategory.mk'_ρ_inv

@[simp]
theorem mk'_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (λ_ X).Hom :=
  rfl
#align category_theory.free_monoidal_category.mk_l_hom CategoryTheory.FreeMonoidalCategory.mk'_l_hom

@[simp]
theorem mk'_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_l_inv CategoryTheory.FreeMonoidalCategory.mk'_l_inv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
  rfl
#align category_theory.free_monoidal_category.tensor_eq_tensor CategoryTheory.FreeMonoidalCategory.tensor_eq_tensor

@[simp]
theorem unit_eq_unit : FreeMonoidalCategory.unit = 𝟙_ (F C) :=
  rfl
#align category_theory.free_monoidal_category.unit_eq_unit CategoryTheory.FreeMonoidalCategory.unit_eq_unit

section Functor

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (f : C → D)

/- warning: category_theory.free_monoidal_category.project_obj -> CategoryTheory.FreeMonoidalCategory.projectObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} D] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u3} D _inst_1], (C -> D) -> (CategoryTheory.FreeMonoidalCategory.{u2} C) -> D
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u2} D] [_inst_2 : CategoryTheory.MonoidalCategory.{u3, u2} D _inst_1], (C -> D) -> (CategoryTheory.FreeMonoidalCategory.{u1} C) -> D
Case conversion may be inaccurate. Consider using '#align category_theory.free_monoidal_category.project_obj CategoryTheory.FreeMonoidalCategory.projectObjₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for `free_monoidal_category.project`. -/
def projectObj : F C → D
  | free_monoidal_category.of X => f X
  | free_monoidal_category.unit => 𝟙_ D
  | free_monoidal_category.tensor X Y => project_obj X ⊗ project_obj Y
#align category_theory.free_monoidal_category.project_obj CategoryTheory.FreeMonoidalCategory.projectObj

section

open Hom

/- warning: category_theory.free_monoidal_category.project_map_aux -> CategoryTheory.FreeMonoidalCategory.projectMapAux is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} {D : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} D] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u3} D _inst_1] (f : C -> D) {X : CategoryTheory.FreeMonoidalCategory.{u2} C} {Y : CategoryTheory.FreeMonoidalCategory.{u2} C}, (CategoryTheory.FreeMonoidalCategory.Hom.{u2} C X Y) -> (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_1)) (CategoryTheory.FreeMonoidalCategory.projectObj.{u1, u2, u3} C D _inst_1 _inst_2 f X) (CategoryTheory.FreeMonoidalCategory.projectObj.{u1, u2, u3} C D _inst_1 _inst_2 f Y))
but is expected to have type
  PUnit.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))}
Case conversion may be inaccurate. Consider using '#align category_theory.free_monoidal_category.project_map_aux CategoryTheory.FreeMonoidalCategory.projectMapAuxₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for `free_monoidal_category.project`. -/
@[simp]
def projectMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (projectObj f X ⟶ projectObj f Y)
  | _, _, id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).Hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).Hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).Hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, comp f g => project_map_aux f ≫ project_map_aux g
  | _, _, hom.tensor f g => project_map_aux f ⊗ project_map_aux g
#align category_theory.free_monoidal_category.project_map_aux CategoryTheory.FreeMonoidalCategory.projectMapAux

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def projectMap (X Y : F C) : (X ⟶ Y) → (projectObj f X ⟶ projectObj f Y) :=
  Quotient.lift (projectMapAux f)
    (by
      intro f g h
      induction' h with
        X Y f X Y f g hfg hfg' X Y f g h _ _ hfg hgh X Y Z f f' g g' _ _ hf hg W X Y Z f g f' g' _ _ hfg hfg'
      · rfl
      · exact hfg'.symm
      · exact hfg.trans hgh
      · simp only [project_map_aux, hf, hg]
      · simp only [project_map_aux, hfg, hfg']
      · simp only [project_map_aux, category.comp_id]
      · simp only [project_map_aux, category.id_comp]
      · simp only [project_map_aux, category.assoc]
      · simp only [project_map_aux, monoidal_category.tensor_id]
        rfl
      · simp only [project_map_aux, monoidal_category.tensor_comp]
      · simp only [project_map_aux, iso.hom_inv_id]
      · simp only [project_map_aux, iso.inv_hom_id]
      · simp only [project_map_aux, monoidal_category.associator_naturality]
      · simp only [project_map_aux, iso.hom_inv_id]
      · simp only [project_map_aux, iso.inv_hom_id]
      · simp only [project_map_aux]
        dsimp [project_obj]
        exact monoidal_category.right_unitor_naturality _
      · simp only [project_map_aux, iso.hom_inv_id]
      · simp only [project_map_aux, iso.inv_hom_id]
      · simp only [project_map_aux]
        dsimp [project_obj]
        exact monoidal_category.left_unitor_naturality _
      · simp only [project_map_aux]
        exact monoidal_category.pentagon _ _ _ _
      · simp only [project_map_aux]
        exact monoidal_category.triangle _ _)
#align category_theory.free_monoidal_category.project_map CategoryTheory.FreeMonoidalCategory.projectMap

end

/-- If `D` is a monoidal category and we have a function `C → D`, then we have a functor from the
    free monoidal category over `C` to the category `D`. -/
def project : MonoidalFunctor (F C) D
    where
  obj := projectObj f
  map := projectMap f
  ε := 𝟙 _
  μ X Y := 𝟙 _
#align category_theory.free_monoidal_category.project CategoryTheory.FreeMonoidalCategory.project

end Functor

end

end FreeMonoidalCategory

end CategoryTheory

