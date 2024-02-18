import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

/-! ## Example use of string diagram widgets -/

section MonoidalCategory

open ProofWidgets

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

lemma left_triangle {X Y : C} (η : 𝟙_ _ ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ _) (w : False) :
    η ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε = (λ_ _).hom ≫ (ρ_ _).inv := by
  with_panel_widgets [SelectionPanel]
    exact w.elim

lemma yang_baxter {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    R V₁ V₂ ▷ V₃ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom =
    (α_ _ ..).hom ≫ V₁ ◁ R V₂ V₃ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ := by
  with_panel_widgets [GoalTypePanel]
    exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : X ⊗ X ⊗ Y ⟶ Y ⊗ X ⊗ Y) (w : False) : f ▷ (X ⊗ Y) = g := by
  with_panel_widgets [SelectionPanel]
    -- the widget does't work
    simp only [MonoidalCategory.whiskerRight_tensor]
    -- now the widget works
    exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : 𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y) (w : False) : 𝟙_ C ◁ f = g := by
  with_panel_widgets [SelectionPanel]
    -- the widget does't work
    simp only [MonoidalCategory.id_whiskerLeft]
    -- now the widget works
    exact w.elim

elab "normalize% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Mathlib.Tactic.Widget.StringDiagram.eval e).e

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

#guard_expr (normalize% (X ◁ 𝟙 Y)) = 𝟙 (X ⊗ Y)
#guard_expr (normalize% (𝟙 X ▷ Y)) = 𝟙 (X ⊗ Y)
#guard_expr (normalize% (X ◁ (f ≫ g))) = X ◁ f ≫ X ◁ g
#guard_expr (normalize% ((f ≫ g) ▷ Y)) = f ▷ Y ≫ g ▷ Y
#guard_expr (normalize% 𝟙_ C ◁ f) = (λ_ _).hom ≫ f ≫ (λ_ _).inv
#guard_expr (normalize% (X ⊗ Y) ◁ f) = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv
#guard_expr (normalize% (f ▷ 𝟙_ C)) = (ρ_ _).hom ≫ f ≫ (ρ_ _).inv
#guard_expr (normalize% f ▷ (X ⊗ Y)) = (α_ _ _ _).inv ≫ f ▷ X ▷ Y ≫ (α_ _ _ _).hom
#guard_expr (normalize% ((X ◁ f) ▷ Y)) = (α_ _ _ _).hom ≫ X ◁ f ▷ Y ≫ (α_ _ _ _).inv
#guard_expr (normalize% (λ_ X).hom) = (λ_ X).hom
#guard_expr (normalize% (λ_ X).inv) = (λ_ X).inv
#guard_expr (normalize% (ρ_ X).hom) = (ρ_ X).hom
#guard_expr (normalize% (ρ_ X).inv) = (ρ_ X).inv
#guard_expr (normalize% (α_ X Y Z).hom) = (α_ _ _ _).hom
#guard_expr (normalize% (α_ X Y Z).inv) = (α_ _ _ _).inv
#guard_expr (normalize% (𝟙 (X ⊗ Y))) = 𝟙 (X ⊗ Y)
