/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.monoidal.free.coherence
! leanprover-community/mathlib commit f187f1074fa1857c94589cc653c786cadc4c35ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Free.Basic
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`full_normalize : free_monoidal_category C ⥤ discrete (normal_monoidal_object C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphismns, but also that they
assemble into a natural isomorphism `𝟭 (free_monoidal_category C) ≅ full_normalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]

-/


universe u

namespace CategoryTheory

open MonoidalCategory

namespace FreeMonoidalCategory

variable {C : Type u}

section

variable (C)

/-- We say an object in the free monoidal category is in normal form if it is of the form
    `(((𝟙_ C) ⊗ X₁) ⊗ X₂) ⊗ ⋯`. -/
@[nolint has_nonempty_instance]
inductive NormalMonoidalObject : Type u
  | Unit : normal_monoidal_object
  | tensor : normal_monoidal_object → C → normal_monoidal_object
#align category_theory.free_monoidal_category.normal_monoidal_object CategoryTheory.FreeMonoidalCategory.NormalMonoidalObject

end

-- mathport name: exprF
local notation "F" => FreeMonoidalCategory

-- mathport name: exprN
local notation "N" => Discrete ∘ NormalMonoidalObject

-- mathport name: «expr ⟶ᵐ »
local infixr:10 " ⟶ᵐ " => Hom

/-- Auxiliary definition for `inclusion`. -/
@[simp]
def inclusionObj : NormalMonoidalObject C → F C
  | normal_monoidal_object.unit => unit
  | normal_monoidal_object.tensor n a => tensor (inclusion_obj n) (of a)
#align category_theory.free_monoidal_category.inclusion_obj CategoryTheory.FreeMonoidalCategory.inclusionObj

/-- The discrete subcategory of objects in normal form includes into the free monoidal category. -/
@[simp]
def inclusion : N C ⥤ F C :=
  Discrete.functor inclusionObj
#align category_theory.free_monoidal_category.inclusion CategoryTheory.FreeMonoidalCategory.inclusion

/-- Auxiliary definition for `normalize`. -/
@[simp]
def normalizeObj : F C → NormalMonoidalObject C → N C
  | Unit, n => ⟨n⟩
  | of X, n => ⟨NormalMonoidalObject.tensor n X⟩
  | tensor X Y, n => normalize_obj Y (normalize_obj X n).as
#align category_theory.free_monoidal_category.normalize_obj CategoryTheory.FreeMonoidalCategory.normalizeObj

@[simp]
theorem normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C)) n = ⟨n⟩ :=
  rfl
#align category_theory.free_monoidal_category.normalize_obj_unitor CategoryTheory.FreeMonoidalCategory.normalizeObj_unitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeObj (X ⊗ Y) n = normalizeObj Y (normalizeObj X n).as :=
  rfl
#align category_theory.free_monoidal_category.normalize_obj_tensor CategoryTheory.FreeMonoidalCategory.normalizeObj_tensor

section

open Hom

attribute [local tidy] tactic.discrete_cases

/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
    associators and unitors map to the same normal form. -/
@[simp]
def normalizeMapAux :
    ∀ {X Y : F C},
      (X ⟶ᵐ Y) → ((Discrete.functor (normalizeObj X) : _ ⥤ N C) ⟶ Discrete.functor (normalizeObj Y))
  | _, _, id _ => 𝟙 _
  | _, _, α_hom _ _ _ =>
    ⟨fun X => 𝟙 _, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | _, _, α_inv _ _ _ =>
    ⟨fun X => 𝟙 _, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | _, _, l_hom _ =>
    ⟨fun X => 𝟙 _, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | _, _, l_inv _ =>
    ⟨fun X => 𝟙 _, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | _, _, ρ_hom _ =>
    ⟨fun ⟨X⟩ => ⟨⟨by simp⟩⟩, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | _, _, ρ_inv _ =>
    ⟨fun ⟨X⟩ => ⟨⟨by simp⟩⟩, by
      rintro ⟨X⟩ ⟨Y⟩ f
      simp⟩
  | X, Y, @comp _ U V W f g => normalize_map_aux f ≫ normalize_map_aux g
  | X, Y, @hom.tensor _ T U V W f g =>
    ⟨fun X =>
      (normalize_map_aux g).app (normalizeObj T X.as) ≫
        (Discrete.functor (normalizeObj W) : _ ⥤ N C).map ((normalize_map_aux f).app X),
      by tidy⟩
#align category_theory.free_monoidal_category.normalize_map_aux CategoryTheory.FreeMonoidalCategory.normalizeMapAux

end

section

variable (C)

/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
    out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
    `𝟙_ C`. -/
@[simp]
def normalize : F C ⥤ N C ⥤ N C
    where
  obj X := Discrete.functor (normalizeObj X)
  map X Y := Quotient.lift normalizeMapAux (by tidy)
#align category_theory.free_monoidal_category.normalize CategoryTheory.FreeMonoidalCategory.normalize

/-- A variant of the normalization functor where we consider the result as an object in the free
    monoidal category (rather than an object of the discrete subcategory of objects in normal
    form). -/
@[simp]
def normalize' : F C ⥤ N C ⥤ F C :=
  normalize C ⋙ (whiskeringRight _ _ _).obj inclusion
#align category_theory.free_monoidal_category.normalize' CategoryTheory.FreeMonoidalCategory.normalize'

/-- The normalization functor for the free monoidal category over `C`. -/
def fullNormalize : F C ⥤ N C
    where
  obj X := ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map X Y f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩
#align category_theory.free_monoidal_category.full_normalize CategoryTheory.FreeMonoidalCategory.fullNormalize

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
    the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
def tensorFunc : F C ⥤ N C ⥤ F C
    where
  obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ ⊗ X
  map X Y f :=
    ⟨fun n => 𝟙 _ ⊗ f, by
      rintro ⟨X⟩ ⟨Y⟩
      tidy⟩
#align category_theory.free_monoidal_category.tensor_func CategoryTheory.FreeMonoidalCategory.tensorFunc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).app n = 𝟙 _ ⊗ f :=
  rfl
#align category_theory.free_monoidal_category.tensor_func_map_app CategoryTheory.FreeMonoidalCategory.tensorFunc_map_app

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C).obj Z).map f = inclusion.map f ⊗ 𝟙 Z :=
  by
  cases n
  cases n'
  tidy
#align category_theory.free_monoidal_category.tensor_func_obj_map CategoryTheory.FreeMonoidalCategory.tensorFunc_obj_map

/-- Auxiliary definition for `normalize_iso`. Here we construct the isomorphism between
    `n ⊗ X` and `normalize X n`. -/
@[simp]
def normalizeIsoApp :
    ∀ (X : F C) (n : N C), ((tensorFunc C).obj X).obj n ≅ ((normalize' C).obj X).obj n
  | of X, n => Iso.refl _
  | Unit, n => ρ_ _
  | tensor X Y, n =>
    (α_ _ _ _).symm ≪≫ tensorIso (normalize_iso_app X n) (Iso.refl _) ≪≫ normalize_iso_app _ _
#align category_theory.free_monoidal_category.normalize_iso_app CategoryTheory.FreeMonoidalCategory.normalizeIsoApp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem normalizeIsoApp_tensor (X Y : F C) (n : N C) :
    normalizeIsoApp C (X ⊗ Y) n =
      (α_ _ _ _).symm ≪≫ tensorIso (normalizeIsoApp C X n) (Iso.refl _) ≪≫ normalizeIsoApp _ _ _ :=
  rfl
#align category_theory.free_monoidal_category.normalize_iso_app_tensor CategoryTheory.FreeMonoidalCategory.normalizeIsoApp_tensor

@[simp]
theorem normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _ :=
  rfl
#align category_theory.free_monoidal_category.normalize_iso_app_unitor CategoryTheory.FreeMonoidalCategory.normalizeIsoApp_unitor

/-- Auxiliary definition for `normalize_iso`. -/
@[simp]
def normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X :=
  NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩
      tidy)
#align category_theory.free_monoidal_category.normalize_iso_aux CategoryTheory.FreeMonoidalCategory.normalizeIsoAux

section

variable {D : Type u} [Category.{u} D] {I : Type u} (f : I → D) (X : Discrete I)

-- TODO: move to discrete_category.lean, decide whether this should be a global simp lemma
@[simp]
theorem discrete_functor_obj_eq_as : (Discrete.functor f).obj X = f X.as :=
  rfl
#align category_theory.free_monoidal_category.discrete_functor_obj_eq_as CategoryTheory.FreeMonoidalCategory.discrete_functor_obj_eq_as

-- TODO: move to discrete_category.lean, decide whether this should be a global simp lemma
@[simp]
theorem discrete_functor_map_eq_id (g : X ⟶ X) : (Discrete.functor f).map g = 𝟙 _ := by tidy
#align category_theory.free_monoidal_category.discrete_functor_map_eq_id CategoryTheory.FreeMonoidalCategory.discrete_functor_map_eq_id

end

/-- The isomorphism between `n ⊗ X` and `normalize X n` is natural (in both `X` and `n`, but
    naturality in `n` is trivial and was "proved" in `normalize_iso_aux`). This is the real heart
    of our proof of the coherence theorem. -/
def normalizeIso : tensorFunc C ≅ normalize' C :=
  NatIso.ofComponents (normalizeIsoAux C)
    (by
      rintro X Y f
      apply Quotient.inductionOn f
      intro f
      ext n
      induction f generalizing n
      · simp only [mk_id, Functor.map_id, category.id_comp, category.comp_id]
      · dsimp
        simp only [id_tensor_associator_inv_naturality_assoc, ← pentagon_inv_assoc,
          tensor_hom_inv_id_assoc, tensor_id, category.id_comp, discrete.functor_map_id,
          comp_tensor_id, iso.cancel_iso_inv_left, category.assoc]
        dsimp
        simp only [category.comp_id]
      · dsimp
        simp only [discrete.functor_map_id, comp_tensor_id, category.assoc, pentagon_inv_assoc, ←
          associator_inv_naturality_assoc, tensor_id, iso.cancel_iso_inv_left]
        dsimp
        simp only [category.comp_id]
      · dsimp
        rw [triangle_assoc_comp_right_assoc]
        simp only [discrete.functor_map_id, category.assoc]
        cases n
        dsimp
        simp only [category.comp_id]
      · dsimp
        simp only [triangle_assoc_comp_left_inv_assoc, inv_hom_id_tensor_assoc, tensor_id,
          category.id_comp, discrete.functor_map_id]
        dsimp
        simp only [category.comp_id]
        cases n
        simp
      · dsimp
        rw [← (iso.inv_comp_eq _).2 (right_unitor_tensor _ _), category.assoc, ←
          right_unitor_naturality]
        simp only [iso.cancel_iso_inv_left, category.assoc]
        congr 1
        convert(category.comp_id _).symm
        convert discrete_functor_map_eq_id inclusion_obj _ _
        ext
        rfl
      · dsimp
        simp only [← (iso.eq_comp_inv _).1 (right_unitor_tensor_inv _ _), right_unitor_conjugation,
          category.assoc, iso.hom_inv_id, iso.hom_inv_id_assoc, iso.inv_hom_id,
          iso.inv_hom_id_assoc]
        congr
        convert(discrete_functor_map_eq_id inclusion_obj _ _).symm
        ext
        rfl
      · dsimp at *
        rw [id_tensor_comp, category.assoc, f_ih_g ⟦f_g⟧, ← category.assoc, f_ih_f ⟦f_f⟧,
          category.assoc, ← functor.map_comp]
        congr 2
      · dsimp at *
        rw [associator_inv_naturality_assoc]
        slice_lhs 2 3 => rw [← tensor_comp, f_ih_f ⟦f_f⟧]
        conv_lhs => rw [← @category.id_comp (F C) _ _ _ ⟦f_g⟧]
        simp only [category.comp_id, tensor_comp, category.assoc]
        congr 2
        rw [← mk_tensor, Quotient.lift_mk]
        dsimp
        rw [functor.map_comp, ← category.assoc, ← f_ih_g ⟦f_g⟧, ←
          @category.comp_id (F C) _ _ _ ⟦f_g⟧, ←
          category.id_comp ((discrete.functor inclusion_obj).map _), tensor_comp]
        dsimp
        simp only [category.assoc, category.comp_id]
        congr 1
        convert(normalize_iso_aux C f_Z).Hom.naturality ((normalize_map_aux f_f).app n)
        exact (tensor_func_obj_map _ _ _).symm)
#align category_theory.free_monoidal_category.normalize_iso CategoryTheory.FreeMonoidalCategory.normalizeIso

/-- The isomorphism between an object and its normal form is natural. -/
def fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion :=
  NatIso.ofComponents
    (fun X => (λ_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [left_unitor_inv_naturality_assoc, category.assoc, iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => nat_trans.app f (discrete.mk normal_monoidal_object.unit))
          ((normalizeIso.{u} C).Hom.naturality f))
#align category_theory.free_monoidal_category.full_normalize_iso CategoryTheory.FreeMonoidalCategory.fullNormalizeIso

end

/-- The monoidal coherence theorem. -/
instance subsingleton_hom : Quiver.IsThin (F C) := fun _ _ =>
  ⟨fun f g =>
    by
    have : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    rw [← functor.id_map f, ← functor.id_map g]
    simp [← nat_iso.naturality_2 (fullNormalizeIso.{u} C), this]⟩
#align category_theory.free_monoidal_category.subsingleton_hom CategoryTheory.FreeMonoidalCategory.subsingleton_hom

section Groupoid

section

open Hom

/-- Auxiliary construction for showing that the free monoidal category is a groupoid. Do not use
    this, use `is_iso.inv` instead. -/
def inverseAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (Y ⟶ᵐ X)
  | _, _, id X => id X
  | _, _, α_hom _ _ _ => α_inv _ _ _
  | _, _, α_inv _ _ _ => α_hom _ _ _
  | _, _, ρ_hom _ => ρ_inv _
  | _, _, ρ_inv _ => ρ_hom _
  | _, _, l_hom _ => l_inv _
  | _, _, l_inv _ => l_hom _
  | _, _, comp f g => (inverse_aux g).comp (inverse_aux f)
  | _, _, hom.tensor f g => (inverse_aux f).tensor (inverse_aux g)
#align category_theory.free_monoidal_category.inverse_aux CategoryTheory.FreeMonoidalCategory.inverseAux

end

instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := fun X Y => Quotient.lift (fun f => ⟦inverseAux f⟧) (by tidy) }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory

