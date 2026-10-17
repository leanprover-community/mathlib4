import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel

/-! # Example use of string diagram widgets -/

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


lemma otp
  {VA VB VE V₁ V₂ V₃ V₄ V₅ : C}
  (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁)
  (zero : ∀ V₁ : C, 𝟙_ C ⟶ V₁)
  (rand : ∀ V₁ : C, 𝟙_ C ⟶ V₁)
  (delete : ∀ V₁ : C, V₁ ⟶ 𝟙_ C)
  (carryforward : ∀ V₁ V₂ : C, V₁ ⟶ V₂)
  (xor : ∀ V₁ V₂ V₃ : C, V₁ ⊗ V₂ ⟶ V₃)
  (copy : ∀ V₁ V₂ V₃ : C, V₁ ⟶ V₂ ⊗ V₃)
  (zero_xor : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₃ ⊗ V₁
    -- The second arrow is V₃ ⊗ V₁ ⟶ V₂
    -- But the V₃ is coming from a zero here so I can use the "left unitor"
    -- The left unitor gives me the arrow V₁ ⟶ 𝟙_ C ⊗ V₁
    -- then I can whisker zero to get 𝟙_ C ⊗ V₁ ⟶ V₃ ⊗ V₁
    -- and then V₃ ⊗ V₁ ⟶ V₂
    -- On the RHS I want to just have an arrow
    (((λ_ V₁).inv ≫ (zero V₃ ▷ V₁) ≫ xor V₃ V₁ V₂) : V₁ ⟶ V₂)
    =
    carryforward V₁ V₂
  )
  (xor_zero : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₁ ⊗ V₃
    -- The second arrow is V₁ ⊗ V₃ ⟶ V₂
    -- But the V₃ is coming from a zero here so I can use the "right unitor"
    -- The right unitor.inv gives me the arrow V₁ ⟶ V₁ ⊗ 𝟙_ C
    -- then I can whisker zero to get V₁ ⊗ 𝟙_ C ⟶ V₁ ⊗ V₃
    -- and then V₁ ⊗ V₃ ⟶ V₂
    -- On the RHS I want to just have an arrow, which I do by carryforward
    (((ρ_ V₁).inv ≫ (V₁ ◁ zero V₃) ≫ xor V₁ V₃ V₂) : V₁ ⟶ V₂)
    =
    carryforward V₁ V₂
  )
  (delete_copy : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₃ ⊗ V₂
    -- The second arrow is V₃ ⊗ V₂ ⟶ V₂
    -- But the V₃ is going to a delete here so I can use the "left unitor"
    -- The first arrow is copy for V₁ ⟶ V₃ ⊗ V₂
    -- The second arrow is V₃ ⊗ V₂ ⟶ 𝟙_ C ⊗ V₂
    -- the left unitor gives me the arrow 𝟙_ C ⊗ V₂ ⟶ V₂
    -- On the RHS I want to just have a carryforward arrow
    (copy V₁ V₃ V₂ ≫ (delete V₃ ▷ V₂) ≫ (λ_ V₂).hom : V₁ ⟶ V₂)
    =
    carryforward V₁ V₂
  )
  (copy_delete : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₂ ⊗ V₃
    -- The second arrow is V₂ ⊗ V₃ ⟶ V₂
    -- But the V₃ is going to a delete here so I can use the "right unitor"
    -- The first arrow is copy for V₁ ⟶ V₂ ⊗ V₃
    -- The second arrow is V₂ ⊗ V₃ ⟶ V₂ ⊗ 𝟙_ C
    -- the right unitor gives me the arrow V₂ ⊗ 𝟙_ C ⟶ V₂
    -- On the RHS I want to just have a carryforward arrow
    (copy V₁ V₂ V₃ ≫ (V₂ ◁ delete V₃) ≫ (ρ_ V₂).hom : V₁ ⟶ V₂)
    =
    carryforward V₁ V₂
  )
  (xor_assoc : ∀ V₁ V₂ V₃ V₄ V₅ V₆ : C,
    -- The final arrow I want is V₁ ⊗ V₂ ⊗ V₃ ⟶ V₄
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⊗ V₂ ⊗ V₃ ⟶ V₁ ⊗ V₅
    -- The second arrow is V₁ ⊗ V₅ ⟶ V₄
    -- On the RHS I want to get this by composing the two arrows:
    -- The first arrow is (V₁ ⊗ V₂) ⊗ V₃ ⟶ V₆ ⊗ V₃
    -- The second arrow is V₆ ⊗ V₃ ⟶ V₄
    -- But this doesn't match due the associativity of the LHS
    -- Therfore, I need to use the "monoidal associator"
    -- The associator inverse gives me the arrow V₁ ⊗ V₂ ⊗ V₃ ⟶ (V₁ ⊗ V₂) ⊗ V₃
    -- then I can compose with (V₁ ⊗ V₂) ⊗ V₃ ⟶ V₆ ⊗ V₃
    -- and then V₆ ⊗ V₃ ⟶ V₄
    (((V₁ ◁ xor V₂ V₃ V₅) ≫ xor V₁ V₅ V₄) : V₁ ⊗ V₂ ⊗ V₃ ⟶ V₄)
    =
    ((α_ _ ..).inv ≫ (xor V₁ V₂ V₆ ▷ V₃) ≫ (xor V₆ V₃ V₄) : V₁ ⊗ V₂ ⊗ V₃ ⟶ V₄)
  )
  (copy_assoc : ∀ V₁ V₂ V₃ V₄ V₅ V₆ : C,
    -- The final arrow I want is V₁ ⟶ V₂ ⊗ V₃ ⊗ V₄
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₂ ⊗ V₅
    -- The second arrow is V₂ ⊗ V₅ ⟶ V₂ ⊗ V₃ ⊗ V₄
    -- On the RHS I want to get this by composing the two arrows:
    -- The first arrow is V₁ ⟶ V₆ ⊗ V₄
    -- The second arrow is V₆ ⊗ V₄ ⟶ (V₂ ⊗ V₃) ⊗ V₄
    -- But this doesn't match due the associativity of the RHS
    -- Therfore, I need to use the "monoidal associator"
    -- The associator gives me the arrow (V₂ ⊗ V₃) ⊗ V₄ ⟶ V₂ ⊗ V₃ ⊗ V₄
    -- then I can compose with V₁ ⟶ (V₂ ⊗ V₃) ⊗ V₄
    -- and then (V₂ ⊗ V₃) ⊗ V₄ ⟶ V₂ ⊗ V₃ ⊗ V₄
    (copy V₁ V₂ V₅ ≫ (V₂ ◁ copy V₅ V₃ V₄) : V₁ ⟶ V₂ ⊗ V₃ ⊗ V₄)
    =
    ((copy V₁ V₆ V₄) ≫ (copy V₆ V₂ V₃ ▷ V₄) ≫ (α_ _ ..).hom : V₁ ⟶ V₂ ⊗ V₃ ⊗ V₄)
  )
  (xor_self : ∀ V₁ V₂ V₃ V₄ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is copy V₁ ⟶ V₃ ⊗ V₄
    -- The second arrow is xor V₃ ⊗ V₄ ⟶ V₂
    -- On the RHS I want to compose
    -- The first arrow is V₁ ⟶ 𝟙_ C
    -- The second arrow is 𝟙_ C ⟶ V₂
    (copy V₁ V₃ V₄ ≫ xor V₃ V₄ V₂ : V₁ ⟶ V₂)
    =
    delete V₁ ≫ zero V₂
  )
  (rand_xor : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₃ ⊗ V₁
    -- The second arrow is V₃ ⊗ V₁ ⟶ V₂
    -- But the V₃ is coming from a rand here so I can use the "left unitor"
    (((λ_ V₁).inv ≫ (rand V₃ ▷ V₁) ≫ xor V₃ V₁ V₂) : V₁ ⟶ V₂)
    =
    delete V₁ ≫ rand V₂
  )
  (xor_rand : ∀ V₁ V₂ V₃ : C,
    -- The final arrow I want is V₁ ⟶ V₂
    -- On the LHS I want to get this by composing two arrows
    -- The first arrow is V₁ ⟶ V₁ ⊗ V₃
    -- The second arrow is V₁ ⊗ V₃ ⟶ V₂
    -- But the V₃ is coming from a rand here so I can use the "right unitor"
    (((ρ_ V₁).inv ≫ (V₁ ◁ rand V₃) ≫ xor V₁ V₃ V₂) : V₁ ⟶ V₂)
    =
    delete V₁ ≫ rand V₂
  )
  (copy_xor_comm : ∀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ V₉ : C,
    -- The final arrow I want is V₁ ⊗ V₂ ⟶ V₃ ⊗ V₄
    ((((copy V₁ V₅ V₆) ⊗ (copy V₂ V₇ V₈)) : (V₁ ⊗ V₂ ⟶ (V₅ ⊗ V₆) ⊗ (V₇ ⊗ V₈)))
      ≫ (𝟙 _ ⊗≫ V₅ ◁ R V₆ V₇ ▷ V₈ ⊗≫ 𝟙 _)
      ≫ (((xor V₅ V₇ V₃) ⊗ (xor V₆ V₈ V₄)) : (V₅ ⊗ V₇) ⊗ (V₆ ⊗ V₈) ⟶ V₃ ⊗ V₄)
       : V₁ ⊗ V₂ ⟶ V₃ ⊗ V₄)
    =
    (xor V₁ V₂ V₉ ≫ copy V₉ V₃ V₄)
  )
  (w : False)
  :
  ((ρ_ VA).inv
    ≫ (VA ◁ rand V₁)
    ≫ (VA ◁ copy V₁ V₂ V₃)
    ≫ ((α_ _ ..).inv)
    ≫ (xor VA V₂ V₄ ▷ V₃)
    ≫ (copy V₄ VE V₅ ▷ V₃)
    ≫ ((α_ _ ..).hom)
    ≫ (VE ◁ xor V₅ V₃ VB)
    : VA ⟶ VE ⊗ VB)
  =
  (λ_ VA).inv ≫ (rand VE ⊗ carryforward VA VB)
  := by
  with_panel_widgets [SelectionPanel]

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
