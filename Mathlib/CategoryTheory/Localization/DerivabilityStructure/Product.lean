import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Localization.Prod

namespace CategoryTheory

open Category Localization

variable {C₁ D₁ C₂ D₂ : Type*} {C₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁ W₁') (Φ₂ : LocalizerMorphism W₂ W₂')

def prod : LocalizerMorphism (W₁.prod W₂) (W₁'.prod W₂') where
  functor := Φ₁.functor.prod Φ₂.functor
  map := fun _ _ ⟨f₁, f₂⟩ ⟨h₁, h₂⟩ => ⟨Φ₁.map f₁ h₁, Φ₂.map f₂ h₂⟩

variable {Φ₁ Φ₂}

def RightResolution.prod {X₁ : D₁} {X₂ : D₂} (R₁ : Φ₁.RightResolution X₁)
    (R₂ : Φ₂.RightResolution X₂) : (Φ₁.prod Φ₂).RightResolution ⟨X₁, X₂⟩ where
  X₁ := ⟨R₁.X₁, R₂.X₁⟩
  w := ⟨R₁.w, R₂.w⟩
  hw := ⟨R₁.hw, R₂.hw⟩

variable (Φ₁ Φ₂)

instance [Φ₁.HasRightResolutions] [Φ₂.HasRightResolutions] :
    (Φ₁.prod Φ₂).HasRightResolutions := fun ⟨X₁, X₂⟩ => by
  refine' ⟨RightResolution.prod _ _⟩
  all_goals apply Classical.arbitrary

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₁'.ContainsIdentities] [W₂'.ContainsIdentities]

instance [Φ₁.IsRightDerivabilityStructure] [Φ₂.IsRightDerivabilityStructure] :
    (Φ₁.prod Φ₂).IsRightDerivabilityStructure := by
  rw [(Φ₁.prod Φ₂).isRightDerivabilityStructure_iff (W₁.Q.prod W₂.Q) (W₁'.Q.prod W₂'.Q)
    ((Φ₁.localizedFunctor W₁.Q W₁'.Q).prod (Φ₂.localizedFunctor W₂.Q W₂'.Q))
    (NatIso.prod (Φ₁.catCommSq W₁.Q W₁'.Q).iso (Φ₂.catCommSq W₂.Q W₂'.Q).iso)]
  have := Φ₁.guitartExact_of_isRightDerivabilityStructure W₁.Q W₁'.Q
  have := Φ₂.guitartExact_of_isRightDerivabilityStructure W₂.Q W₂'.Q
  apply TwoSquare.GuitartExact.prod

end LocalizerMorphism

end CategoryTheory
