import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel
import Mathlib.Tactic.CategoryTheory.Coherence

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
  with_panel_widgets [SelectionPanel]
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

end MonoidalCategory
