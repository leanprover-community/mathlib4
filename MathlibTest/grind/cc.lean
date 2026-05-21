module

example (a₁ a₂ b₁ b₂ c d : Nat) :
        a₁ = c → a₂ = c →
        b₁ = d → d = b₂ →
        a₁ + b₁ + a₁ = a₂ + b₂ + c := by
  grind

example (a b c : Prop) : (a ↔ b) → ((a ∧ (c ∨ b)) ↔ (b ∧ (c ∨ a))) := by
  grind

example (a b c d : Prop)
    [d₁ : Decidable a] [d₂ : Decidable b] [d₃ : Decidable c] [d₄ : Decidable d] :
    (a ↔ b) → (c ↔ d) →
      ((if (a ∧ c) then True else False) ↔ (if (b ∧ d) then True else False)) := by
  grind

example (a b : Nat) : (a = b) = (b = a) := by
  grind

section Lean3Issue1442

def Rel : Int × Int → Int × Int → Prop
  | (n₁, d₁), (n₂, d₂) => n₁ * d₂ = n₂ * d₁

def mul' : Int × Int → Int × Int → Int × Int
  | (n₁, d₁), (n₂, d₂) => ⟨n₁ * n₂, d₁ * d₂⟩

example : ∀ (a b c d : Int × Int), Rel a c → Rel b d → Rel (mul' a b) (mul' c d) :=
  fun (n₁, d₁) (n₂, d₂) (n₃, d₃) (n₄, d₄) =>
    fun (h₁ : n₁ * d₃ = n₃ * d₁) (h₂ : n₂ * d₄ = n₄ * d₂) =>
      show (n₁ * n₂) * (d₃ * d₄) = (n₃ * n₄) * (d₁ * d₂) by
        grind

end Lean3Issue1442
