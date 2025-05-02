/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedThree
import Mathlib.CategoryTheory.Functor.Quadrifunctor

/-!
# Composition with a left derived trifunctor
-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₂₃₄ C D₁ D₂ D₃ D₄ D₂₃₄ D : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₂₃₄] [Category C]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category D₂₃₄] [Category D]
  {LF : D₁ ⥤ D₂₃₄ ⥤ D} {LG₂₃₄ : D₂ ⥤ D₃ ⥤ D₄ ⥤ D₂₃₄}
  {F : C₁ ⥤ C₂₃₄ ⥤ C} {G₂₃₄ : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄} {L₂₃₄ : C₂₃₄ ⥤ D₂₃₄} {L : C ⥤ D}
  (α : ((((whiskeringLeft₃ D₂₃₄).obj L₂).obj L₃).obj L₄).obj LG₂₃₄ ⟶ G₂₃₄ ⋙
    Functor.postcompose₂.obj L₂₃₄)
  (β : (((whiskeringLeft₂ D).obj L₁).obj L₂₃₄).obj LF ⟶ F ⋙ (whiskeringRight _ _ _).obj L)


set_option maxHeartbeats 3200000 in
-- this is slow
@[simps]
def trifunctorComp₂₃₄Counit :
    (((((whiskeringLeft₄ D).obj L₁).obj L₂).obj L₃).obj L₄).obj (trifunctorComp₂₃₄ LF LG₂₃₄) ⟶
      (Functor.postcompose₄.obj L).obj (trifunctorComp₂₃₄ F G₂₃₄) where
  app X₁ :=
    { app X₂ :=
      { app X₃ :=
        { app X₄ := (LF.obj (L₁.obj X₁)).map (((α.app X₂).app X₃).app X₄) ≫
            (β.app X₁).app (((G₂₃₄.obj X₂).obj X₃).obj X₄)
          naturality X₄ Y₄ f₄ := by
            have hα := ((α.app X₂).app X₃).naturality f₄
            have hβ := (β.app X₁).naturality (((G₂₃₄.obj X₂).obj X₃).map f₄)
            dsimp at hα hβ ⊢
            rw [Category.assoc, ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc, hβ] }
        naturality X₃ Y₃ f₃ := by
          ext X₄
          have hα := congr_app ((α.app X₂).naturality f₃) X₄
          have hβ := (β.app X₁).naturality (((G₂₃₄.obj X₂).map f₃).app X₄)
          dsimp at hα hβ ⊢
          rw [Category.assoc, ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc, hβ] }
      naturality X₂ Y₂ f₂ := by
        ext X₃ X₄
        have hα := congr_app (congr_app (α.naturality f₂) X₃) X₄
        have hβ := (β.app X₁).naturality (((G₂₃₄.map f₂).app X₃).app X₄)
        dsimp at hα hβ ⊢
        rw [Category.assoc, ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc, hβ] }
  naturality X₁ Y₁ f₁ := by
    ext X₂ X₃ X₄
    have hβ := congr_app (β.naturality f₁) (((G₂₃₄.obj X₂).obj X₃).obj X₄)
    dsimp at hβ ⊢
    rw [Category.assoc, ← NatTrans.naturality_assoc, hβ]

end CategoryTheory
