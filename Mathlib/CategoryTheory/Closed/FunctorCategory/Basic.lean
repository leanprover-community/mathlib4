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
  [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom C F₁ F₂]

attribute [local simp] enrichedCategorySelf_hom enrichedCategorySelf_id
  enrichedCategorySelf_comp enrichedOrdinaryCategorySelf_eHomWhiskerLeft
  enrichedOrdinaryCategorySelf_eHomWhiskerRight

section

variable {F₁ F₂ F₂' F₃ F₃' : J ⥤ C}

/-- The bijection `(F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃)` when `F₁`, `F₂`
and `F₃` are functors `J ⥤ C`, and `C` is monoidal closed. -/
noncomputable def homEquiv : (F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  toFun f :=
    { app := fun j ↦ end_.lift (fun k ↦ F₂.map k.hom ≫ curry (f.app k.right)) (fun k₁ k₂ φ ↦ by
        dsimp
        simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
          enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        rw [← curry_natural_left_assoc, ← curry_natural_left_assoc,
          ← curry_natural_right, curry_pre_app, Category.assoc,
          ← f.naturality φ.right, Monoidal.tensorObj_map, tensorHom_def_assoc,
          ← Under.w φ, Functor.map_comp, MonoidalCategory.whiskerLeft_comp_assoc,
          whisker_exchange_assoc])
      naturality := fun j j' φ ↦ by
        dsimp
        ext k
        dsimp
        rw [Category.assoc, Category.assoc, end_.lift_π]
        erw [end_.lift_π]
        rw [end_.lift_π]
        dsimp
        rw [Functor.map_comp, Category.assoc] }
  invFun g :=
    { app := fun j ↦ uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)) )
      naturality := fun j j' φ ↦ by
        dsimp
        rw [← uncurry_natural_right, tensorHom_def'_assoc, ← uncurry_pre_app,
          ← uncurry_natural_left, Category.assoc, Category.assoc,
          NatTrans.naturality_assoc, functorEnrichedHom_map]
        erw [end_.lift_π_assoc]
        congr 2
        dsimp
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight,
          ← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by
    dsimp
    ext j
    dsimp
    rw [end_.lift_π]
    dsimp
    rw [Functor.map_id, Category.id_comp, uncurry_curry]
  right_inv g := by
    ext j
    dsimp
    ext k
    rw [end_.lift_π, curry_uncurry, NatTrans.naturality_assoc]
    dsimp
    erw [end_.lift_π]
    congr
    dsimp [Under.map, Comma.mapLeft]
    simp only [Category.comp_id]
    rfl

lemma homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃) :
    homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g := by
  dsimp [homEquiv]
  ext j
  dsimp
  rw [← uncurry_natural_left]
  congr 1
  simp only [Category.assoc]

lemma homEquiv_naturality_three [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
    (f : F₁ ⊗ F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') :
    homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ _).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫
      functorEnrichedComp C F₁ F₃ F₃' := by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc, Category.assoc, Category.assoc, end_.lift_π, enrichedComp_π,
    tensorHom_def, Category.assoc, whisker_exchange_assoc,
    MonoidalCategory.whiskerRight_id_assoc, Iso.inv_hom_id_assoc, end_.lift_π_assoc,
    Category.assoc]
  dsimp
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, functorHomEquiv_app_π, curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

end

variable [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
attribute [local instance] Enriched.FunctorCategory.functorEnrichedOrdinaryCategory

/-- When `F : J ⥤ C`, `C` is monoidal closed and has suitable limits,
then `tensorLeft F` has a right adjoint. -/
noncomputable def adj (F : J ⥤ C) :
    MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F⟩ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

/-- When `F : J ⥤ C`, `C` is monoidal closed and has suitable limits,
then `tensorLeft F` has a right adjoint. -/
noncomputable def closed (F : J ⥤ C) : Closed F where
  rightAdj := (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

noncomputable instance monoidalClosed : MonoidalClosed (J ⥤ C) where
  closed := closed

end FunctorCategory

end MonoidalClosed

end CategoryTheory
