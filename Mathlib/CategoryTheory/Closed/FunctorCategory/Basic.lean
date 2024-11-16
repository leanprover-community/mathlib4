/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Closed.Enrichment
import Mathlib.CategoryTheory.Enriched.FunctorCategory

/-!
# Functor categories are monoidal closed

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory

namespace MonoidalClosed

namespace FunctorCategory

open Enriched.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {J : Type u₂} [Category.{v₂} J]
  [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
  [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom C F₁ F₂]

attribute [local simp] enrichedCategorySelf_hom enrichedCategorySelf_id
  enrichedCategorySelf_comp enrichedOrdinaryCategorySelf_eHomWhiskerLeft
  enrichedOrdinaryCategorySelf_eHomWhiskerRight

section

variable {F₁ F₂ F₂' F₃ F₃' : J ⥤ C}

noncomputable def homEquiv : (F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  toFun f :=
    { app := fun j ↦ end_.lift (fun k ↦ F₂.map k.hom ≫ curry (f.app k.right)) (fun k₁ k₂ φ ↦ by
        dsimp
        simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
          enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        rw [← curry_natural_left_assoc, ← curry_natural_left_assoc,
          ← curry_natural_right, curry_pre_app]
        congr 1
        convert (_ ◁ (F₂.map k₁.hom)) ≫= (f.naturality φ.right).symm using 1
        · simp only [Category.assoc]
        · dsimp
          rw [tensorHom_def_assoc, whisker_exchange_assoc,
            ← MonoidalCategory.whiskerLeft_comp_assoc, ← Under.w φ, Functor.map_comp])
      naturality := fun j j' φ ↦ by
        dsimp
        ext k
        dsimp
        rw [Category.assoc, Category.assoc, end_.lift_π]
        erw [precompEnrichedHom_π]
        rw [end_.lift_π]
        dsimp
        rw [Functor.map_comp, Category.assoc] }
  invFun g :=
    { app := fun j ↦ uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)) )
      naturality := sorry }
  left_inv := sorry
  right_inv := sorry

lemma homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃) :
    homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g :=
  sorry

lemma homEquiv_naturality_three (f : F₁ ⊗ F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') :
    homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ _).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫
      functorEnrichedComp C F₁ F₃ F₃' :=
  sorry

end

attribute [local instance] Enriched.FunctorCategory.functorEnrichedOrdinaryCategory

noncomputable def adj (F : J ⥤ C) :
    MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F⟩ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

noncomputable def closed (F : J ⥤ C) : Closed F where
  rightAdj := (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

noncomputable instance monoidalClosed : MonoidalClosed (J ⥤ C) where
  closed := closed

end FunctorCategory

end MonoidalClosed

end CategoryTheory
