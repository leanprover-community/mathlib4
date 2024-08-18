import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

open CategoryTheory

universe v u

section Monoidal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
open scoped MonoidalCategory

example : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by monoidal_coherence
example : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by monoidal_coherence
example (X Y Z : C) : (α_ X Y Z).hom = (α_ X Y Z).hom := by monoidal_coherence
example (X Y Z : C) : (α_ X Y Z).inv = (α_ X Y Z).inv := by monoidal_coherence
example (X Y Z : C) : (α_ X Y Z).inv ≫ (α_ X Y Z).hom = 𝟙 (X ⊗ Y ⊗ Z) := by monoidal_coherence
example (X Y Z W : C) :
    (𝟙 X ⊗ (α_ Y Z W).hom) ≫ (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv =
      (α_ X (Y ⊗ Z) W).inv ≫ ((α_ X Y Z).inv ⊗ 𝟙 W) := by
  monoidal_coherence
example (X Y : C) :
    (X ◁ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  monoidal_coherence
example (X Y : C) :
    (𝟙 X ⊗ (λ_ Y).inv) ≫ 𝟙 X ▷ (𝟙_ C ⊗ Y) ⊗≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  monoidal_coherence
example (X Y : C) :
    (𝟙 X ⊗ (λ_ Y).inv) ≫ ⊗𝟙 ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y := by
  monoidal_coherence

example (X₁ X₂ : C) :
    (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
      (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) ≫
        (𝟙 (𝟙_ C) ⊗ (λ_ _).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 X₂) ≫
          (𝟙 (𝟙_ C) ⊗ (α_ X₁ (𝟙_ C) X₂).hom) ≫
            (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
              ((λ_ X₁).hom ≫ (ρ_ X₁).inv ⊗ 𝟙 (𝟙_ C ⊗ X₂)) ≫
                (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
                  (𝟙 X₁ ⊗ 𝟙 (𝟙_ C) ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
                    (𝟙 X₁ ⊗ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫
                      (𝟙 X₁ ⊗ (λ_ X₂).hom ≫ (ρ_ X₂).inv ⊗ 𝟙 (𝟙_ C)) ≫
                        (𝟙 X₁ ⊗ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom) ≫
                          (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv =
    (((λ_ (𝟙_ C)).hom ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv) ≫
      (𝟙 (X₁ ⊗ X₂) ⊗ (λ_ (𝟙_ C)).inv) := by
  monoidal_coherence

end Monoidal
