/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift

namespace CategoryTheory

namespace NatTrans

namespace CommShift

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
  {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃}
  (α : F₁₃ ⟶ F₁₂ ⋙ F₂₃)
  {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃}
  (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  (e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂)
  (e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃)
  (e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃)
  (A : Type*) [AddMonoid A] [HasShift C₁ A] [HasShift C₂ A] [HasShift C₃ A]
  [HasShift D₁ A] [HasShift D₂ A] [HasShift D₃ A]
  [F₁₂.CommShift A] [F₂₃.CommShift A] [F₁₃.CommShift A] [CommShift α A]
  [G₁₂.CommShift A] [G₂₃.CommShift A] [G₁₃.CommShift A] [CommShift β A]
  [CommShift e₁₂ A]
  (h : e₁₃ = CategoryTheory.whiskerRight α L₃ ≫ (Functor.associator _ _ _).hom ≫
    CategoryTheory.whiskerLeft F₁₂ e₂₃ ≫ (Functor.associator _ _ _).inv ≫
      CategoryTheory.whiskerRight e₁₂ G₂₃ ≫ (Functor.associator _ _ _).hom ≫
        CategoryTheory.whiskerLeft L₁ β)

def verticalComposition : 0 = 1 := by
  sorry

end CommShift

end NatTrans

end CategoryTheory
