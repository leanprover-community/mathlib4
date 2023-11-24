import Mathlib.Tactic.ProdAssoc

variable {α β γ δ : Type*}

example : (α × β) × (γ × δ) ≃ α × (β × γ) × δ := by
  have := (prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)
  exact this

example : (α × β) × (γ × δ) ≃ α × (β × γ) × δ := prod_assoc%

example : (α × β) × (γ × δ) ≃ α × (β × γ) × δ :=
  (prod_assoc% : _ ≃ α × β × γ × δ).trans prod_assoc%

example {α β γ δ : Type*} (x : (α × β) × (γ × δ)) : α × (β × γ) × δ := prod_assoc% x

example : Nat ≃ Nat := prod_assoc%

example (x : α) (y : β) (z : γ) (w : δ) :
    prod_assoc% ((x,y),(z,w)) = (x,y,z,w) :=
  rfl

example (x : α) (y : β) (z : γ) (w : δ) :
    prod_assoc% ((x,y),(z,w)) = (x,(y,z),w) :=
  rfl

example : (α × β) × (γ × δ) → α × (β × γ) × δ :=
  prod_assoc%
