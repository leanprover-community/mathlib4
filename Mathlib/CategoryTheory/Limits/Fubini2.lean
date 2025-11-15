/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Fubini

/-!
# Variant of the Fubini theorem for colimits

-/


open CategoryTheory Functor

namespace CategoryTheory.Limits.DiagramOfCocones

variable {J K C : Type*} [Category J] [Category K] [Category C]

section

variable {F : J ⥤ K ⥤ C} (D : DiagramOfCocones F)
  (hD : ∀ j, IsColimit (D.obj j)) (c : Cocone D.coconePoints)

@[simps]
def coconeUncurryOfCoconeCoconePoints : Cocone (uncurry.obj F) where
  pt := c.pt
  ι.app z := (D.obj z.1).ι.app z.2 ≫ c.ι.app z.1
  ι.naturality := by
    rintro ⟨z₁, z₂⟩ ⟨w₁, w₂⟩ ⟨f₁ : z₁ ⟶ w₁, f₂ : z₂ ⟶ w₂⟩
    have := c.w f₁
    dsimp at this
    simp [← this]

def isColimitCoconeUncurryOfCoconeCoconePoints (hc : IsColimit c) :
    IsColimit (coconeUncurryOfCoconeCoconePoints D c) :=
  IsColimit.ofCoconeUncurry hD (IsColimit.ofIsoColimit hc
    (Cocones.ext (Iso.refl _) (fun j ↦ (hD j).hom_ext (by simp))))

end

def isColimitFubiniFlip
    {F : J ⥤ K ⥤ C} (D₁ : DiagramOfCocones F) (D₂ : DiagramOfCocones F.flip)
    (hD₁ : ∀ j, IsColimit (D₁.obj j)) (hD₂ : ∀ k, IsColimit (D₂.obj k))
    {c₂ : Cocone D₂.coconePoints} (hc₂ : IsColimit c₂)
    {c₁ : Cocone D₁.coconePoints} (e : c₁.pt ≅ c₂.pt)
    (h : ∀ (j : J) (k : K), (D₁.obj j).ι.app k ≫ c₁.ι.app j ≫ e.hom =
      (D₂.obj k).ι.app j ≫ c₂.ι.app k := by cat_disch) :
    IsColimit c₁ := by
  let iso : (Prod.braiding J K).functor ⋙ uncurry.obj F.flip ≅ uncurry.obj F :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let H := (IsColimit.precomposeHomEquiv iso.symm _).2
    ((isColimitCoconeUncurryOfCoconeCoconePoints
      D₂ hD₂ c₂ hc₂).whiskerEquivalence (Prod.braiding J K))
  exact IsColimit.ofIsoColimit (coconeOfCoconeUncurryIsColimit hD₁ H)
    (Cocones.ext e (fun j ↦ (hD₁ j).hom_ext (by cat_disch))).symm

end CategoryTheory.Limits.DiagramOfCocones
