import Mathlib.RingTheory.Valuation.Basic

section LinearOrderedCommMonoidWithZero

variable {R : Type*} [Ring R]
  {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂]
  {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
  (h : v₁.IsEquiv v₂)
  {x x₁ x₂ y y₁ y₂ z w : R}

include h

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

example (r : R) (h1 : v₁ r < 1) : v₂ r < 1 := by
  rw_val_equiv h at h1
  guard_hyp h1 :ₛ v₂ r < 1
  guard_target =ₛ v₂ r < 1
  exact h1

example (r : R) (h1 : v₁ r < 1) : v₂ r < 1 := by
  rw_val_equiv ← h
  guard_hyp h1 :ₛ v₁ r < 1
  guard_target =ₛ v₁ r < 1
  exact h1

example (x y z : R) (h1 : v₁ x < 1) (h2 : 1 < v₂ y) (h3 : v₁ z < 1) :
    v₂ x < 1 ∧ 1 < v₁ y ∧ v₂ z < 1 := by
  rw_val_equiv h at h1 h3 ⊢
  exact ⟨h1, h2, h3⟩

example (x y z : R) (h1 : v₁ x < 1) (h2 : 1 < v₂ y) (h3 : v₁ z < 1) :
    v₂ x < 1 ∧ 1 < v₁ y ∧ v₂ z < 1 := by
  rw_val_equiv ← h at h2 ⊢
  exact ⟨h1, h2, h3⟩

example (x : R) (h1 : v₁ x < 1) : v₂ x < 1 := by
  rwa_val_equiv h at h1

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

set_option trace.rw_val_equiv true in
/--
trace: [rw_val_equiv] Transformed:
    ((Valuation.map f hf v₁) x < 1)
    to:
    (v₁ x < 1)
-/
#guard_msgs in
omit h in
example {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (f : Γ₁ →*₀ Γ₀) (hf : Monotone f) (h : v₁.IsEquiv (v₁.map f hf)) :
    {x | v₁.map f hf x < 1} = {x | v₁ x < 1} := by
  rw_val_equiv h.symm

end LinearOrderedCommGroupWithZero
