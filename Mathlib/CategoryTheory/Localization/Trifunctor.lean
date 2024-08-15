import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Associator

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₄] [Category C₁₂] [Category C₂₃]

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

def bifunctorComp₁₂Iso : bifunctorComp₁₂ F₁₂ G ≅ curry.obj (uncurry.obj F₁₂ ⋙ G) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)

def bifunctorComp₂₃Iso : bifunctorComp₂₃ F G₂₃ ≅ sorry :=
  sorry

end CategoryTheory
