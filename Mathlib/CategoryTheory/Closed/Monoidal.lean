/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.closed.monoidal
! leanprover-community/mathlib commit c0e00a871b9f6d3aca7c10fb3abdc8720a2c5313
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Mates
import Mathbin.CategoryTheory.Functor.InvIsos

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/


universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

-- Note that this class carries a particular choice of right adjoint,
-- (which is only unique up to isomorphism),
-- not merely the existence of such, and
-- so definitional properties of instances may be important.
/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  isAdj : IsLeftAdjoint (tensorLeft X)
#align category_theory.closed CategoryTheory.Closed

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed' : ∀ X : C, Closed X
#align category_theory.monoidal_closed CategoryTheory.MonoidalClosed

attribute [instance] monoidal_closed.closed'

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X ⊗ Y)
    where isAdj := by
    haveI := hX.is_adj
    haveI := hY.is_adj
    exact adjunction.left_adjoint_of_nat_iso (monoidal_category.tensor_left_tensor _ _).symm
#align category_theory.tensor_closed CategoryTheory.tensorClosed

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unitClosed : Closed (𝟙_ C)
    where isAdj :=
    { right := 𝟭 C
      adj :=
        Adjunction.mkOfHomEquiv
          { homEquiv := fun X _ =>
              { toFun := fun a => (leftUnitor X).inv ≫ a
                invFun := fun a => (leftUnitor X).Hom ≫ a
                left_inv := by tidy
                right_inv := by tidy }
            homEquiv_naturality_left_symm := fun X' X Y f g =>
              by
              dsimp
              rw [left_unitor_naturality_assoc] } }
#align category_theory.unit_closed CategoryTheory.unitClosed

variable (A B : C) {X X' Y Y' Z : C}

variable [Closed A]

/-- This is the internal hom `A ⟶[C] -`.
-/
def ihom : C ⥤ C :=
  (@Closed.isAdj _ _ _ A _).right
#align category_theory.ihom CategoryTheory.ihom

namespace Ihom

/-- The adjunction between `A ⊗ -` and `A ⟹ -`. -/
def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.isAdj.adj
#align category_theory.ihom.adjunction CategoryTheory.ihom.adjunction

/-- The evaluation natural transformation. -/
def ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihom.adjunction A).counit
#align category_theory.ihom.ev CategoryTheory.ihom.ev

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A :=
  (ihom.adjunction A).Unit
#align category_theory.ihom.coev CategoryTheory.ihom.coev

@[simp]
theorem ihom_adjunction_counit : (ihom.adjunction A).counit = ev A :=
  rfl
#align category_theory.ihom.ihom_adjunction_counit CategoryTheory.ihom.ihom_adjunction_counit

@[simp]
theorem ihom_adjunction_unit : (ihom.adjunction A).Unit = coev A :=
  rfl
#align category_theory.ihom.ihom_adjunction_unit CategoryTheory.ihom.ihom_adjunction_unit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    (𝟙 A ⊗ (ihom A).map f) ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f
#align category_theory.ihom.ev_naturality CategoryTheory.ihom.ev_naturality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (𝟙 A ⊗ f) :=
  (coev A).naturality f
#align category_theory.ihom.coev_naturality CategoryTheory.ihom.coev_naturality

-- mathport name: ihom
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem ev_coev : (𝟙 A ⊗ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  Adjunction.left_triangle_components (ihom.adjunction A)
#align category_theory.ihom.ev_coev CategoryTheory.ihom.ev_coev

@[simp, reassoc.1]
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A)
#align category_theory.ihom.coev_ev CategoryTheory.ihom.coev_ev

end Ihom

open CategoryTheory.Limits

instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjointPreservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace MonoidalClosed

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Currying in a monoidal closed category. -/
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X) :=
  (ihom.adjunction A).homEquiv _ _
#align category_theory.monoidal_closed.curry CategoryTheory.MonoidalClosed.curry

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Uncurrying in a monoidal closed category. -/
def uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X) :=
  ((ihom.adjunction A).homEquiv _ _).symm
#align category_theory.monoidal_closed.uncurry CategoryTheory.MonoidalClosed.uncurry

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f :=
  rfl
#align category_theory.monoidal_closed.hom_equiv_apply_eq CategoryTheory.MonoidalClosed.homEquiv_apply_eq

@[simp]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
    ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl
#align category_theory.monoidal_closed.hom_equiv_symm_apply_eq CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc.1]
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry ((𝟙 _ ⊗ f) ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _
#align category_theory.monoidal_closed.curry_natural_left CategoryTheory.MonoidalClosed.curry_natural_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc.1]
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihom _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _
#align category_theory.monoidal_closed.curry_natural_right CategoryTheory.MonoidalClosed.curry_natural_right

@[reassoc.1]
theorem uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _
#align category_theory.monoidal_closed.uncurry_natural_right CategoryTheory.MonoidalClosed.uncurry_natural_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc.1]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
    uncurry (f ≫ g) = (𝟙 _ ⊗ f) ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _
#align category_theory.monoidal_closed.uncurry_natural_left CategoryTheory.MonoidalClosed.uncurry_natural_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).left_inv f
#align category_theory.monoidal_closed.uncurry_curry CategoryTheory.MonoidalClosed.uncurry_curry

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).right_inv f
#align category_theory.monoidal_closed.curry_uncurry CategoryTheory.MonoidalClosed.curry_uncurry

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq _ f g
#align category_theory.monoidal_closed.curry_eq_iff CategoryTheory.MonoidalClosed.curry_eq_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply _ f g
#align category_theory.monoidal_closed.eq_curry_iff CategoryTheory.MonoidalClosed.eq_curry_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (𝟙 A ⊗ g) ≫ (ihom.ev A).app X :=
  Adjunction.homEquiv_counit _
#align category_theory.monoidal_closed.uncurry_eq CategoryTheory.MonoidalClosed.uncurry_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  Adjunction.homEquiv_unit _
#align category_theory.monoidal_closed.curry_eq CategoryTheory.MonoidalClosed.curry_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
  (Closed.isAdj.adj.homEquiv _ _).Injective
#align category_theory.monoidal_closed.curry_injective CategoryTheory.MonoidalClosed.curry_injective

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
  (Closed.isAdj.adj.homEquiv _ _).symm.Injective
#align category_theory.monoidal_closed.uncurry_injective CategoryTheory.MonoidalClosed.uncurry_injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  rw [uncurry_eq, tensor_id, id_comp]
#align category_theory.monoidal_closed.uncurry_id_eq_ev CategoryTheory.MonoidalClosed.uncurry_id_eq_ev

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X :=
  by
  rw [curry_eq, (ihom A).map_id (A ⊗ _)]
  apply comp_id
#align category_theory.monoidal_closed.curry_id_eq_coev CategoryTheory.MonoidalClosed.curry_id_eq_coev

section Pre

variable {A B} [Closed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  transferNatTransSelf (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)
#align category_theory.monoidal_closed.pre CategoryTheory.MonoidalClosed.pre

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    (𝟙 B ⊗ (pre f).app X) ≫ (ihom.ev B).app X = (f ⊗ 𝟙 (A ⟶[C] X)) ≫ (ihom.ev A).app X :=
  transferNatTransSelf_counit _ _ ((tensoringLeft C).map f) X
#align category_theory.monoidal_closed.id_tensor_pre_app_comp_ev CategoryTheory.MonoidalClosed.id_tensor_pre_app_comp_ev

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = (f ⊗ 𝟙 _) ≫ (ihom.ev A).app X := by
  rw [uncurry_eq, id_tensor_pre_app_comp_ev]
#align category_theory.monoidal_closed.uncurry_pre CategoryTheory.MonoidalClosed.uncurry_pre

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc.1]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihom.coev B).app X ≫ (ihom B).map (f ⊗ 𝟙 _) :=
  unit_transferNatTransSelf _ _ ((tensoringLeft C).map f) X
#align category_theory.monoidal_closed.coev_app_comp_pre_app CategoryTheory.MonoidalClosed.coev_app_comp_pre_app

@[simp]
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ :=
  by
  simp only [pre, Functor.map_id]
  dsimp
  simp
#align category_theory.monoidal_closed.pre_id CategoryTheory.MonoidalClosed.pre_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, transfer_nat_trans_self_comp, (tensoring_left C).map_comp]
#align category_theory.monoidal_closed.pre_map CategoryTheory.MonoidalClosed.pre_map

theorem pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z := by simp
#align category_theory.monoidal_closed.pre_comm_ihom_map CategoryTheory.MonoidalClosed.pre_comm_ihom_map

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C
    where
  obj X := ihom X.unop
  map X Y f := pre f.unop
#align category_theory.monoidal_closed.internal_hom CategoryTheory.MonoidalClosed.internalHom

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

/-- Transport the property of being monoidal closed across a monoidal equivalence of categories -/
noncomputable def ofEquiv (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor]
    [h : MonoidalClosed D] : MonoidalClosed C
    where closed' X :=
    {
      isAdj := by
        haveI q : closed (F.to_functor.obj X) := inferInstance
        haveI : is_left_adjoint (tensor_left (F.to_functor.obj X)) := q.is_adj
        have i := comp_inv_iso (monoidal_functor.comm_tensor_left F X)
        exact adjunction.left_adjoint_of_nat_iso i }
#align category_theory.monoidal_closed.of_equiv CategoryTheory.MonoidalClosed.ofEquiv

end OfEquiv

end MonoidalClosed

end CategoryTheory

