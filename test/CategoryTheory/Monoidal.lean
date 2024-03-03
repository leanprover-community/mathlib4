import Mathlib.Tactic.CategoryTheory.Monoidal

open CategoryTheory MonoidalCategory Mathlib.Tactic.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)

#guard_expr normalize% X ◁ 𝟙 Y = X ◁ 𝟙 Y
#guard_expr normalize% 𝟙 X ▷ Y = 𝟙 X ▷ Y
#guard_expr normalize% X ◁ (f ≫ g) = _ ≫ X ◁ f ≫ _ ≫ X ◁ g ≫ _
#guard_expr normalize% (f ≫ g) ▷ Y = _ ≫ f ▷ Y ≫ _ ≫ g ▷ Y ≫ _
#guard_expr normalize% 𝟙_ C ◁ f = _ ≫ f ≫ _
#guard_expr normalize% (X ⊗ Y) ◁ f = _ ≫ X ◁ Y ◁ f ≫ _
#guard_expr normalize% f ▷ 𝟙_ C = _ ≫ f ≫ _
#guard_expr normalize% f ▷ (X ⊗ Y) = _ ≫ f ▷ X ▷ Y ≫ _
#guard_expr normalize% (X ◁ f) ▷ Y = _ ≫ X ◁ f ▷ Y ≫ _
#guard_expr normalize% (λ_ X).hom = (λ_ X).hom
#guard_expr normalize% (λ_ X).inv = (λ_ X).inv
#guard_expr normalize% (ρ_ X).hom = (ρ_ X).hom
#guard_expr normalize% (ρ_ X).inv = (ρ_ X).inv
#guard_expr normalize% (α_ X Y Z).hom = (α_ _ _ _).hom
#guard_expr normalize% (α_ X Y Z).inv = (α_ _ _ _).inv
#guard_expr normalize% 𝟙 (X ⊗ Y) = 𝟙 (X ⊗ Y)
#guard_expr normalize% f ⊗ g = _ ≫ f ▷ _ ≫ _ ≫ _ ◁ g ≫ _
variable {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) in
#guard_expr normalize% R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ = _ ≫ R V₁ V₂ ▷ V₃ ≫ _ ≫ V₂ ◁ R V₁ V₃ ≫ _
