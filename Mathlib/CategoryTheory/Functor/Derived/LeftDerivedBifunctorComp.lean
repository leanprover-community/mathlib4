/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedThree

/-!
# Composition of left derived bifunctor

-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₁₂ C₂₃ C D₁ D₂ D₃ D₁₂ D₂₃ D : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₁₂] [Category C₂₃] [Category C]
  [Category D₁] [Category D₂] [Category D₃] [Category D₁₂] [Category D₂₃] [Category D]
  {LF₁₂ : D₁ ⥤ D₂ ⥤ D₁₂} {LG : D₁₂ ⥤ D₃ ⥤ D} {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C}
  {LF : D₁ ⥤ D₂₃ ⥤ D} {LG₂₃ : D₂ ⥤ D₃ ⥤ D₂₃} {F : C₁ ⥤ C₂₃ ⥤ C} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₁₂ : C₁₂ ⥤ D₁₂} {L₂₃ : C₂₃ ⥤ D₂₃} {L : C ⥤ D}
  (α₁₂ : (((whiskeringLeft₂ D₁₂).obj L₁).obj L₂).obj LF₁₂ ⟶ F₁₂ ⋙ (whiskeringRight _ _ _).obj L₁₂)
  (β₁₂ : (((whiskeringLeft₂ D).obj L₁₂).obj L₃).obj LG ⟶ G ⋙ (whiskeringRight _ _ _).obj L)
  (α₂₃ : (((whiskeringLeft₂ D₂₃).obj L₂).obj L₃).obj LG₂₃ ⟶ G₂₃ ⋙ (whiskeringRight _ _ _).obj L₂₃)
  (β₂₃ : (((whiskeringLeft₂ D).obj L₁).obj L₂₃).obj LF ⟶ F ⋙ (whiskeringRight _ _ _).obj L)

@[simps]
def bifunctorComp₁₂Counit :
    (((((whiskeringLeft₃ _).obj L₁).obj L₂)).obj L₃).obj (bifunctorComp₁₂ LF₁₂ LG) ⟶
      (Functor.postcompose₃.obj L).obj (bifunctorComp₁₂ F₁₂ G) where
  app X₁ :=
    { app X₂ :=
      { app X₃ := (LG.map ((α₁₂.app X₁).app X₂)).app (L₃.obj X₃) ≫
          (β₁₂.app ((F₁₂.obj X₁).obj X₂)).app X₃
        naturality {X₃ Y₃} f₃ := by
          have := (β₁₂.app ((F₁₂.obj X₁).obj X₂)).naturality f₃
          dsimp at this ⊢
          simp only [NatTrans.naturality_assoc, Category.assoc, this] }
      naturality {X₂ Y₂} f₂ := by
        ext X₃
        have h₁ := congr_app (β₁₂.naturality ((F₁₂.obj X₁).map f₂)) X₃
        have h₂ := ((α₁₂.app X₁).naturality f₂)
        dsimp at h₁ h₂ ⊢
        rw [Category.assoc, ← h₁, ← NatTrans.comp_app_assoc, ← Functor.map_comp, h₂,
          Functor.map_comp, NatTrans.comp_app_assoc] }
  naturality {X₁ Y₁} f₁ := by
    ext X₂ X₃
    have h₁ := congr_app (β₁₂.naturality ((F₁₂.map f₁).app X₂)) X₃
    have h₂ := congr_app (α₁₂.naturality f₁) X₂
    dsimp at h₁ h₂ ⊢
    rw [Category.assoc, ← h₁, ← NatTrans.comp_app_assoc, ← Functor.map_comp, h₂,
      Functor.map_comp, NatTrans.comp_app_assoc]

set_option maxHeartbeats 400000 in
-- this is slow
@[simps]
def bifunctorComp₂₃Counit :
    (((((whiskeringLeft₃ _).obj L₁).obj L₂)).obj L₃).obj (bifunctorComp₂₃ LF LG₂₃) ⟶
      (Functor.postcompose₃.obj L).obj (bifunctorComp₂₃ F G₂₃) where
  app X₁ :=
    { app X₂ :=
      { app X₃ := (LF.obj (L₁.obj X₁)).map ((α₂₃.app X₂).app X₃) ≫
          (β₂₃.app X₁).app ((G₂₃.obj X₂).obj X₃)
        naturality {X₃ Y₃} f₃ := by
          have h₁ := (β₂₃.app X₁).naturality (((G₂₃.obj X₂).map f₃))
          have h₂ := (α₂₃.app X₂).naturality f₃
          dsimp at h₁ h₂ ⊢
          rw [Category.assoc, ← h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc] }
      naturality {X₂ Y₂} f₂ := by
        ext X₃
        have h₁ := (β₂₃.app X₁).naturality ((G₂₃.map f₂).app X₃)
        have h₂ := congr_app (α₂₃.naturality f₂) X₃
        dsimp at h₁ h₂ ⊢
        rw [Category.assoc, ← h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc] }
  naturality {X₁ Y₁} f₁ := by
    ext X₂ X₃
    have h₁ := congr_app (β₂₃.naturality f₁) ((G₂₃.obj X₂).obj X₃)
    dsimp at h₁ ⊢
    rw [Category.assoc, ← h₁, NatTrans.naturality_assoc]

end CategoryTheory
