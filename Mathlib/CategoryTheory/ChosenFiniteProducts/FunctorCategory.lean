/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Functor categories have chosen finite products

If `C` is a category with chosen finite products, then so is `J ⥤ C`.

-/

namespace CategoryTheory

open Limits MonoidalCategory Category

variable (J C : Type*) [Category J] [Category C] [ChosenFiniteProducts C]

namespace Functor

/-- The chosen terminal object in `J ⥤ C`. -/
abbrev chosenTerminal : J ⥤ C := (Functor.const J).obj (𝟙_ C)

/-- The chosen terminal object in `J ⥤ C` is terminal. -/
def chosenTerminalIsTerminal : IsTerminal (chosenTerminal J C) :=
  evaluationJointlyReflectsLimits _
    (fun _ => isLimitChangeEmptyCone _ ChosenFiniteProducts.terminal.2 _ (Iso.refl _))

section

variable {J C}
variable (F₁ F₂ : J ⥤ C)

/-- The chosen binary product on `J ⥤ C`. -/
@[simps]
def chosenProd : J ⥤ C where
  obj j := F₁.obj j ⊗ F₂.obj j
  map φ := F₁.map φ ⊗ F₂.map φ

namespace chosenProd

/-- The first projection `chosenProd F₁ F₂ ⟶ F₁`. -/
def fst : chosenProd F₁ F₂ ⟶ F₁ where
  app _ := ChosenFiniteProducts.fst _ _

/-- The second projection `chosenProd F₁ F₂ ⟶ F₂`. -/
def snd : chosenProd F₁ F₂ ⟶ F₂ where
  app _ := ChosenFiniteProducts.snd _ _

/-- `Functor.chosenProd F₁ F₂` is a binary product of `F₁` and `F₂`. -/
def isLimit : IsLimit (BinaryFan.mk (fst F₁ F₂) (snd F₁ F₂)) :=
  evaluationJointlyReflectsLimits _ (fun j =>
    (IsLimit.postcomposeHomEquiv (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
      (IsLimit.ofIsoLimit (ChosenFiniteProducts.product (X := F₁.obj j) (Y := F₂.obj j)).2
        (Cones.ext (Iso.refl _) (by rintro ⟨_|_⟩; all_goals aesop_cat))))

end chosenProd

end

instance chosenFiniteProducts :
    ChosenFiniteProducts (J ⥤ C) where
  terminal := ⟨_, chosenTerminalIsTerminal J C⟩
  product F₁ F₂ := ⟨_, chosenProd.isLimit F₁ F₂⟩

namespace Monoidal

open ChosenFiniteProducts

variable {J C}

@[simp]
lemma tensorObj_obj (F₁ F₂ : J ⥤ C) (j : J) : (F₁ ⊗ F₂).obj j = (F₁.obj j) ⊗ (F₂.obj j) := rfl

@[simp]
lemma tensorObj_map (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j') :
    (F₁ ⊗ F₂).map f = (F₁.map f) ⊗ (F₂.map f) := rfl

@[simp]
lemma fst_app (F₁ F₂ : J ⥤ C) (j : J) : (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.obj j) := rfl

@[simp]
lemma snd_app (F₁ F₂ : J ⥤ C) (j : J) : (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.obj j) := rfl

@[simp]
lemma leftUnitor_hom_app (F : J ⥤ C) (j : J) :
    (λ_ F).hom.app j = (λ_ (F.obj j)).hom := rfl

@[simp]
lemma leftUnitor_inv_app (F : J ⥤ C) (j : J) :
    (λ_ F).inv.app j = (λ_ (F.obj j)).inv := by
  rw [← cancel_mono ((λ_ (F.obj j)).hom), Iso.inv_hom_id, ← leftUnitor_hom_app,
    Iso.inv_hom_id_app]

@[simp]
lemma rightUnitor_hom_app (F : J ⥤ C) (j : J) :
    (ρ_ F).hom.app j = (ρ_ (F.obj j)).hom := rfl

@[simp]
lemma rightUnitor_inv_app (F : J ⥤ C) (j : J) :
    (ρ_ F).inv.app j = (ρ_ (F.obj j)).inv := by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom), Iso.inv_hom_id, ← rightUnitor_hom_app,
    Iso.inv_hom_id_app]

@[reassoc (attr := simp)]
lemma tensorHom_app_fst {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ g).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  change (f ⊗ g).app j ≫ (fst F₁' F₂').app j = _
  rw [← NatTrans.comp_app, tensorHom_fst, NatTrans.comp_app]
  rfl

@[reassoc (attr := simp)]
lemma tensorHom_app_snd {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f ⊗ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  change (f ⊗ g).app j ≫ (snd F₁' F₂').app j = _
  rw [← NatTrans.comp_app, tensorHom_snd, NatTrans.comp_app]
  rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_app_fst (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ fst _ _ = fst _ _ :=
  (tensorHom_app_fst (𝟙 F₁) g j).trans (by simp)

@[reassoc (attr := simp)]
lemma whiskerLeft_app_snd (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j :=
  (tensorHom_app_snd (𝟙 F₁) g j)

@[reassoc (attr := simp)]
lemma whiskerRight_app_fst {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ fst _ _ = fst _ _ ≫ f.app j :=
  (tensorHom_app_fst f (𝟙 F₂) j)

@[reassoc (attr := simp)]
lemma whiskerRight_app_snd {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ snd _ _ = snd _ _ :=
  (tensorHom_app_snd f (𝟙 F₂) j).trans (by simp)

@[simp]
lemma associator_hom_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).hom.app j = (α_ _ _ _).hom := by
  apply hom_ext
  · rw [← fst_app, ← NatTrans.comp_app, associator_hom_fst]
    simp
  · apply hom_ext
    · rw [← snd_app, ← NatTrans.comp_app, ← fst_app, ← NatTrans.comp_app, Category.assoc,
        associator_hom_snd_fst]
      simp
    · rw [← snd_app, ← NatTrans.comp_app, ← snd_app, ← NatTrans.comp_app, Category.assoc,
        associator_hom_snd_snd]
      simp

@[simp]
lemma associator_inv_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).inv.app j = (α_ _ _ _).inv := by
  rw [← cancel_mono ((α_ _ _ _).hom), Iso.inv_hom_id, ← associator_hom_app, Iso.inv_hom_id_app]

instance {K : Type*} [Category K] [HasColimitsOfShape K C]
    [∀ X : C, PreservesColimitsOfShape K (tensorLeft X)] {F : J ⥤ C} :
    PreservesColimitsOfShape K (tensorLeft F) := by
  apply preservesColimitsOfShape_of_evaluation
  intro k
  haveI : tensorLeft F ⋙ (evaluation J C).obj k ≅ (evaluation J C).obj k ⋙ tensorLeft (F.obj k) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact preservesColimitsOfShape_of_natIso this.symm

end Monoidal

end Functor

end CategoryTheory
