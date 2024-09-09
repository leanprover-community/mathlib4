import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel

/-! ## Example use of string diagram widgets -/

section MonoidalCategory

open ProofWidgets Mathlib.Tactic.Widget

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

lemma left_triangle {X Y : C} (η : 𝟙_ _ ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ _) (w : False) :
    η ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε = (λ_ _).hom ≫ (ρ_ _).inv := by
  /- Displays string diagrams for the both sides of the goal. -/
  with_panel_widgets [StringDiagram]
    /- Place the cursor here to see the string diagrams. -/
    /- You can also see the string diagram of any 2-morphism in the goal or hyperthesis. -/
    with_panel_widgets [SelectionPanel]
      /- Place the cursor here and shift-click the 2-morphisms in the tactic state. -/
      exact w.elim

/- Instead of writing `with_panel_widgets` everywhere, you can also use this command. -/
show_panel_widgets [local StringDiagram, local SelectionPanel]

lemma yang_baxter {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    R V₁ V₂ ▷ V₃ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom =
    (α_ _ ..).hom ≫ V₁ ◁ R V₂ V₃ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ := by
  /- Place the cursor here to see the string diagrams. -/
  exact w.elim

lemma yang_baxter' {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ ⊗≫ R V₂ V₃ ▷ V₁ ⊗≫ 𝟙 _ =
    𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ⊗≫ R V₁ V₃ ▷ V₂ ⊗≫ V₃ ◁ R V₁ V₂ := by
  exact w.elim

lemma yang_baxter'' {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    (R V₁ V₂ ⊗ 𝟙 V₃) ≫ (α_ _ ..).hom ≫
      (𝟙 V₂ ⊗ R V₁ V₃) ≫ (α_ _ ..).inv ≫
        (R V₂ V₃ ⊗ 𝟙 V₁) ≫ (α_ _ ..).hom =
      (α_ _ ..).hom ≫ (𝟙 V₁ ⊗ R V₂ V₃) ≫
        (α_ _ ..).inv ≫ (R V₁ V₃ ⊗ 𝟙 V₂) ≫
          (α_ _ ..).hom ≫ (𝟙 V₃ ⊗ R V₁ V₂) := by
  exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : X ⊗ X ⊗ Y ⟶ Y ⊗ X ⊗ Y) (w : False) : f ▷ (X ⊗ Y) = g := by
  exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : 𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y) (w : False) : 𝟙_ C ◁ f = g := by
  exact w.elim

example {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ := by
  rw [MonoidalCategory.whisker_exchange]
  rw [MonoidalCategory.tensorHom_def]

end MonoidalCategory
