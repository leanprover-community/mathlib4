/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Chosen finite products on sheaves

In this file, we put a `CartesianMonoidalCategory` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a `CartesianMonoidalCategory` instance.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Category Limits Sieve MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [CartesianMonoidalCategory A]

namespace Sheaf
variable (X Y : Sheaf J A)

lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.obj ⊗ Y.obj) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

instance : ObjectProperty.IsMonoidal (Presheaf.IsSheaf J (A := A)) where
  prop_unit := tensorUnit_isSheaf _
  prop_tensor F G hF hG := tensorProd_isSheaf J ⟨F, hF⟩ ⟨G, hG⟩

example : CartesianMonoidalCategory (Sheaf J A) :=
  inferInstance


@[simp] lemma cartesianMonoidalCategoryFst_hom : (fst X Y).hom = fst X.obj Y.obj := rfl
@[simp] lemma cartesianMonoidalCategorySnd_hom : (snd X Y).hom = snd X.obj Y.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryFst_val := cartesianMonoidalCategoryFst_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategorySnd_val := cartesianMonoidalCategorySnd_hom

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

@[simp] lemma cartesianMonoidalCategoryLift_hom : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerLeft_hom : (X ◁ f).hom = X.obj ◁ f.hom := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerRight_hom : (f ▷ X).hom = f.hom ▷ X.obj := rfl

@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryLift_val := cartesianMonoidalCategoryLift_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerLeft_val := cartesianMonoidalCategoryWhiskerLeft_hom
@[deprecated (since := "2026-03-05")]
alias cartesianMonoidalCategoryWhiskerRight_val := cartesianMonoidalCategoryWhiskerRight_hom

end Sheaf

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}

@[simp] lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory
