import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Functor.Currying

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂]
  [Category D₁] [Category D₂] [Category E]

@[simps!]
def curryObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (G : D₁ × D₂ ⥤ E) :
    curry.obj ((F₁.prod F₂).comp G) ≅
      F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C₂ D₂ E).obj F₂ :=
  NatIso.ofComponents (fun X₁ => NatIso.ofComponents (fun X₂ => Iso.refl _))

@[simps!]
def whiskeringLeft₂ObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (E : Type*) [Category E] :
    (D₁ ⥤ D₂ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ E) :=
  (whiskeringRight D₁ (D₂ ⥤ E) (C₂ ⥤ E)).obj ((whiskeringLeft C₂ D₂ E).obj F₂) ⋙
    (whiskeringLeft C₁ D₁ (C₂ ⥤ E)).obj F₁

namespace MorphismProperty

def IsInvertedBy₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

end MorphismProperty

namespace Localization

variable (F : C₁ ⥤ C₂ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (hF : MorphismProperty.IsInvertedBy₂ W₁ W₂ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

noncomputable def lift₂ : D₁ ⥤ D₂ ⥤ E :=
  curry.obj (lift (uncurry.obj F) hF (L₁.prod L₂))

noncomputable def fac₂ : (whiskeringLeft₂ObjObj L₁ L₂ E).obj (lift₂ F hF L₁ L₂) ≅ F :=
  (curryObjProdComp _ _ _).symm ≪≫
    curry.mapIso (fac (uncurry.obj F) hF (L₁.prod L₂)) ≪≫
    currying.unitIso.symm.app F

end Localization

end CategoryTheory
