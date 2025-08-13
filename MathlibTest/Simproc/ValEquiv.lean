import Mathlib.RingTheory.Valuation.Basic

section LinearOrderedCommMonoidWithZero

variable {R : Type*} [Ring R]
  {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂]
  {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
  (h : v₁.IsEquiv v₂)
  {x x₁ x₂ y y₁ y₂ z w : R}

example {x1 x2 x3 y1 y2 y3 : R}
    (h' : min (v₁ x1) (v₁ y1) * min (v₁ x2) (v₁ y2) * min (v₁ x3) (v₁ y3) < 1) :
    min (v₂ x1) (v₂ y1) * min (v₂ x2) (v₂ y2) * min (v₂ x3) (v₂ y3) < 1 := by
  rw_val_equiv h.symm
  exact h'

omit h in
example {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (f : Γ₁ →*₀ Γ₀) (hf : Monotone f) (h : v₁.IsEquiv (v₁.map f hf)) :
    {x | v₁.map f hf x < 1} = {x | v₁ x < 1} := by
  rw_val_equiv h.symm

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero

variable {R : Type*} [Ring R]
  {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
  {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
  (h : v₁.IsEquiv v₂)
  {x x₁ x₂ y y₁ y₂ z w : R}

example {x : R} : v₁ x ^ (-3 : ℤ) ≤ 1 ↔ v₂ x ^ (-3 : ℤ) ≤ 1 := by
  rw_val_equiv h

example {x1 x2 x3 y1 y2 y3 : R}
    (h' : min (v₁ x1) (v₁ y1) * min (v₁ x2) (v₁ y2) * min (v₁ x3) (v₁ y3) < 1) :
    min (v₂ x1) (v₂ y1) * min (v₂ x2) (v₂ y2) * min (v₂ x3) (v₂ y3) < 1 := by
  rw_val_equiv h.symm
  exact h'

example : v₁ x / (v₁ y)⁻¹ < v₁ z ↔ v₂ x / (v₂ y)⁻¹ < v₂ z := by
  rw_val_equiv h

omit h in
example {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (f : Γ₁ →*₀ Γ₀) (hf : Monotone f) (h : v₁.IsEquiv (v₁.map f hf)) :
    {x | v₁.map f hf x < 1} = {x | v₁ x < 1} := by
  rw_val_equiv h.symm

end LinearOrderedCommGroupWithZero
