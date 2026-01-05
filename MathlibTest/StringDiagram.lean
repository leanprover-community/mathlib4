import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel

/-! ## Example use of string diagram widgets -/

open ProofWidgets Mathlib.Tactic.Widget

section MonoidalCategory

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section

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
    (R V₁ V₂ ⊗ₘ 𝟙 V₃) ≫ (α_ _ ..).hom ≫
      (𝟙 V₂ ⊗ₘ R V₁ V₃) ≫ (α_ _ ..).inv ≫
        (R V₂ V₃ ⊗ₘ 𝟙 V₁) ≫ (α_ _ ..).hom =
      (α_ _ ..).hom ≫ (𝟙 V₁ ⊗ₘ R V₂ V₃) ≫
        (α_ _ ..).inv ≫ (R V₁ V₃ ⊗ₘ 𝟙 V₂) ≫
          (α_ _ ..).hom ≫ (𝟙 V₃ ⊗ₘ R V₁ V₂) := by
  exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : X ⊗ X ⊗ Y ⟶ Y ⊗ X ⊗ Y) (w : False) : f ▷ (X ⊗ Y) = g := by
  exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : 𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y) (w : False) : 𝟙_ C ◁ f = g := by
  exact w.elim

example {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f ⊗ₘ g = X₁ ◁ g ≫ f ▷ Y₂ := by
  rw [MonoidalCategory.whisker_exchange]
  rw [MonoidalCategory.tensorHom_def]

end

set_option trace.string_diagram true

variable {C : Type u} [Category.{v} C] [i : MonoidalCategory C] {X Y : C}

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_1_1)

[string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_1_1)
-/
#guard_msgs (whitespace := lax) in
#string_diagram MonoidalCategory.whisker_exchange

/-- trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)

[string_diagram] Penrose substance: Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
-/
#guard_msgs (whitespace := lax) in
#string_diagram MonoidalCategory.whisker_exchange_assoc

/--
trace: [string_diagram] Penrose substance:

[string_diagram] Penrose substance:
-/
#guard_msgs (whitespace := lax) in
#string_diagram MonoidalCategory.pentagon

/--
trace: [string_diagram] Penrose substance:

[string_diagram] Penrose substance:
-/
#guard_msgs (whitespace := lax) in
#string_diagram MonoidalCategory.whiskerLeft_id

/--
trace: [string_diagram] Penrose substance:
    Left(E_1_0_0, E_1_0_2)
    Left(E_2_0_0, E_2_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_2)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
    Mor1 f_1_4 := MakeString (E_1_0_2, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)

[string_diagram] Penrose substance:
-/
#guard_msgs (whitespace := lax) in
#string_diagram left_triangle

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_2_2)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_2_2)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_0_0)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_2_2)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
    Mor1 f_1_4 := MakeString (E_1_2_2, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_2_3 := MakeString (E_2_1_1, E_3_2_2)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_1 := MakeString (E_3_0_0, E_4_1_1)
    Mor1 f_3_4 := MakeString (E_3_2_2, E_4_2_2)

[string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_2_2)
    Left(E_3_0_0, E_3_1_1)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_0_0)
    Mor1 f_1_3 := MakeString (E_1_1_1, E_2_2_2)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_1 := MakeString (E_2_0_0, E_3_1_1)
    Mor1 f_2_4 := MakeString (E_2_2_2, E_3_1_1)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_2 := MakeString (E_3_1_1, E_4_1_1)
    Mor1 f_3_3 := MakeString (E_3_1_1, E_4_2_2)
-/
#guard_msgs (whitespace := lax) in
#string_diagram yang_baxter

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_2_2)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_2_2)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_0_0)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_2_2)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
    Mor1 f_1_4 := MakeString (E_1_2_2, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_2_3 := MakeString (E_2_1_1, E_3_2_2)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_1 := MakeString (E_3_0_0, E_4_1_1)
    Mor1 f_3_4 := MakeString (E_3_2_2, E_4_2_2)

[string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_2_2)
    Left(E_3_0_0, E_3_1_1)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_0_0)
    Mor1 f_1_3 := MakeString (E_1_1_1, E_2_2_2)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_1 := MakeString (E_2_0_0, E_3_1_1)
    Mor1 f_2_4 := MakeString (E_2_2_2, E_3_1_1)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_2 := MakeString (E_3_1_1, E_4_1_1)
    Mor1 f_3_3 := MakeString (E_3_1_1, E_4_2_2)
-/
#guard_msgs (whitespace := lax) in
#string_diagram yang_baxter'

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_2_2)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_2_2)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_0_0)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_2_2)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
    Mor1 f_1_4 := MakeString (E_1_2_2, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_2_3 := MakeString (E_2_1_1, E_3_2_2)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_1 := MakeString (E_3_0_0, E_4_1_1)
    Mor1 f_3_4 := MakeString (E_3_2_2, E_4_2_2)

[string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_2_2)
    Left(E_3_0_0, E_3_1_1)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_0_0)
    Mor1 f_1_3 := MakeString (E_1_1_1, E_2_2_2)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_1 := MakeString (E_2_0_0, E_3_1_1)
    Mor1 f_2_4 := MakeString (E_2_2_2, E_3_1_1)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_2 := MakeString (E_3_1_1, E_4_1_1)
    Mor1 f_3_3 := MakeString (E_3_1_1, E_4_2_2)
-/
#guard_msgs (whitespace := lax) in
#string_diagram yang_baxter''

/--
trace: [string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)

[string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
-/
#guard_msgs (whitespace := lax) in
#string_diagram Category.assoc

/--
trace: [string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)

[string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
-/
#guard_msgs (whitespace := lax) in
#string_diagram Functor.map_comp

/--
trace: [string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)

[string_diagram] Penrose substance:
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
-/
#guard_msgs (whitespace := lax) in
#string_diagram NatTrans.naturality

variable (f : 𝟙_ _ ⟶ X ⊗ Y) in
/--
trace: [string_diagram] Penrose substance:
    Left(E_2_0_0, E_2_1_1)
    Above(E_1_0_0, E_2_0_0)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
-/
#guard_msgs (whitespace := lax) in
#string_diagram f

variable (g : Y ⊗ X ⟶ 𝟙_ _) in
/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Above(E_0_0_0, E_1_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_0_0)
-/
#guard_msgs (whitespace := lax) in
#string_diagram g

abbrev yangBaxterLhs {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) :=
  R V₁ V₂ ▷ V₃ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_0_1_1, E_0_2_2)
    Left(E_1_0_0, E_1_2_2)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_2_2)
    Left(E_4_0_0, E_4_1_1)
    Left(E_4_1_1, E_4_2_2)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Above(E_3_0_0, E_4_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_0_0)
    Mor1 f_0_4 := MakeString (E_0_2_2, E_1_2_2)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_1 := MakeString (E_1_0_0, E_2_1_1)
    Mor1 f_1_4 := MakeString (E_1_2_2, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_0_0)
    Mor1 f_2_3 := MakeString (E_2_1_1, E_3_2_2)
    Mor1 f_3_0 := MakeString (E_3_0_0, E_4_0_0)
    Mor1 f_3_1 := MakeString (E_3_0_0, E_4_1_1)
    Mor1 f_3_4 := MakeString (E_3_2_2, E_4_2_2)
-/
#guard_msgs (whitespace := lax) in
#string_diagram yangBaxterLhs

end MonoidalCategory

section Bicategory

open CategoryTheory

set_option trace.string_diagram true

/--
trace: [string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_1_1)

[string_diagram] Penrose substance:
    Left(E_0_0_0, E_0_1_1)
    Left(E_1_0_0, E_1_1_1)
    Left(E_2_0_0, E_2_1_1)
    Left(E_3_0_0, E_3_1_1)
    Above(E_0_0_0, E_1_0_0)
    Above(E_1_0_0, E_2_0_0)
    Above(E_2_0_0, E_3_0_0)
    Mor1 f_0_0 := MakeString (E_0_0_0, E_1_0_0)
    Mor1 f_0_2 := MakeString (E_0_1_1, E_1_1_1)
    Mor1 f_1_0 := MakeString (E_1_0_0, E_2_0_0)
    Mor1 f_1_2 := MakeString (E_1_1_1, E_2_1_1)
    Mor1 f_2_0 := MakeString (E_2_0_0, E_3_0_0)
    Mor1 f_2_2 := MakeString (E_2_1_1, E_3_1_1)
-/
#guard_msgs (whitespace := lax) in
#string_diagram Bicategory.whisker_exchange

end Bicategory
