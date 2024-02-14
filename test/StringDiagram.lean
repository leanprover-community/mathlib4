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

def left_triangle {X Y : C} (η : 𝟙_ _ ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ _) (w : False) :
    η ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε = (λ_ _).hom ≫ (ρ_ _).inv := by
  with_panel_widgets [SelectionPanel]
    exact w.elim

def yang_baxter {V : C} (R : V ⊗ V ⟶ V ⊗ V) (w : False) :
    R ▷ V ≫ (α_ _ _ _).hom ≫ V ◁ R ≫ (α_ _ _ _).inv ≫ (R ▷ V) ≫ (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ V ◁ R ≫ (α_ _ _ _).inv ≫ (R ▷ V) ≫ (α_ _ _ _).hom ≫ (V ◁ R) := by
  with_panel_widgets [SelectionPanel]
    exact w.elim
