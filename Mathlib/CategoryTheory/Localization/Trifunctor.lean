import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Functor.Trifunctor

namespace CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (W : MorphismProperty C) (L : C ⥤ D)

variable {E E' : Type*} [Category E] [Category E']

variable (F : C ⥤ C ⥤ C) (G : C ⥤ C ⥤ C)

-- #check bifunctorComp₁₂ F G
-- #check bifunctorComp₂₃ F G

variable (hF : W.IsInvertedBy₂ W ((whiskeringRight₂' C C L).obj F))
  (hG : W.IsInvertedBy₂ W ((whiskeringRight₂' C C L).obj G))

variable [L.IsLocalization W] [W.ContainsIdentities]

-- #check lift₂ ((whiskeringRight₂' C C L).obj F) hF L L
-- #check lift₂ _ hG L L

-- #check bifunctorComp₁₂ (lift₂ ((whiskeringRight₂' C C L).obj F) hF L L) (lift₂ _ hG L L)
-- #check bifunctorComp₂₃ (lift₂ ((whiskeringRight₂' C C L).obj F) hF L L) (lift₂ _ hG L L)


def associator : bifunctorComp₁₂ (lift₂ _ hF L L) (lift₂ _ hG L L) ≅
  bifunctorComp₂₃ (lift₂ _ hF L L) (lift₂ _ hG L L) := sorry

section

variable {C₁ C₂ C₃: Type*} [Category C₁] [Category C₂] [Category C₃]

variable {D₁ D₂ D₃ : Type*} [Category D₁] [Category D₂] [Category D₃]

variable {E E' : Type*} [Category E] [Category E']

def _root_.CategoryTheory.MorphismProperty.IsInvertedBy₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy₂ W₃ (uncurry.obj F)

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}
  (hF : MorphismProperty.IsInvertedBy₃ W₁ W₂ W₃ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

noncomputable def lift₃ : D₁ ⥤ D₂ ⥤ D₃ ⥤ E :=
  curry.obj (lift₂ (uncurry.obj F) hF (L₁.prod L₂) L₃)

end

end

end Localization

end CategoryTheory
