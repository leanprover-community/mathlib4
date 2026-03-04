/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits

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
  apply isSheaf_of_isLimit (E := (Cones.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

/-- Any `CartesianMonoidalCategory` on `A` induce a
`CartesianMonoidalCategory` structure on `A`-valued sheaves. -/
noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory (Sheaf J A) :=
  .ofChosenFiniteProducts
    ({ cone := asEmptyCone ⟨𝟙_ (Cᵒᵖ ⥤ A), tensorUnit_isSheaf _⟩
       isLimit.lift f := ObjectProperty.homMk (toUnit f.pt.obj)
       isLimit.fac := by rintro _ ⟨⟨⟩⟩
       isLimit.uniq x f h := InducedCategory.hom_ext (toUnit_unique f.hom _) })
  fun X Y ↦ {
    cone := BinaryFan.mk
        (P := ⟨X.obj ⊗ Y.obj, tensorProd_isSheaf J X Y⟩)
        (ObjectProperty.homMk (fst _ _)) (ObjectProperty.homMk (snd _ _))
    isLimit.lift f := ObjectProperty.homMk
      (lift (BinaryFan.fst f).hom (BinaryFan.snd f).hom)
    isLimit.fac := by
      rintro s ⟨⟨j⟩⟩ <;> apply InducedCategory.hom_ext <;> simp
    isLimit.uniq x f h := by
      apply InducedCategory.hom_ext
      apply CartesianMonoidalCategory.hom_ext
      · specialize h ⟨.left⟩
        rw [InducedCategory.Hom.ext_iff] at h
        simpa using h
      · specialize h ⟨.right⟩
        rw [InducedCategory.Hom.ext_iff] at h
        simpa using h
  }

@[simp] lemma cartesianMonoidalCategoryFst_hom : (fst X Y).hom = fst X.obj Y.obj := rfl
@[simp] lemma cartesianMonoidalCategorySnd_hom : (snd X Y).hom = snd X.obj Y.obj := rfl

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

@[simp] lemma cartesianMonoidalCategoryLift_hom : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerLeft_hom : (X ◁ f).hom = X.obj ◁ f.hom := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerRight_hom : (f ▷ X).hom = f.hom ▷ X.obj := rfl

end Sheaf

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion from sheaves to presheaves is monoidal with respect to the Cartesian monoidal
structures. -/
noncomputable instance sheafToPresheafMonoidal : (sheafToPresheaf J A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := .refl _
      μIso F G := .refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}

@[simp] lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory
