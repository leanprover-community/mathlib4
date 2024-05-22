import Mathlib.Tactic.CancelDenoms
import Mathlib.Tactic.Ring

private axiom test_sorry : ∀ {α}, α
universe u
section
variable {α : Type u} [LinearOrderedField α] (a b c d : α)

-- prior to #12083, `cancel_denoms` would not make progress on this
example : ¬ (4 / 2 : ℚ) = 3 := by cancel_denoms

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h

example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring

example (h : 0 < a) : a / (3/2) > 0 := by
  cancel_denoms
  exact h

example (h : 0 < a): 0 < a / 1 := by
  cancel_denoms
  exact h

example (h : a < 0): 0 < a / -1 := by
  cancel_denoms
  exact h

example (h : -a < 2 * b): a / -2 < b := by
  cancel_denoms
  exact h

example (h : a < 6 * a) : a / 2 / 3 < a := by
  cancel_denoms
  exact h

example (h : a < 9 * a) : a / 3 / 3 < a := by
  cancel_denoms
  exact h

end

-- Some tests with a concrete type universe.
section
variable {α : Type} [LinearOrderedField α] (a b c d : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h

variable {α : Type} [Field α] [CharZero α] (a b c d : α)
example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring
end

-- Some tests with a concrete type.
section
variable (a b c d : ℚ)

-- inspired by automated testing
example : (1 : ℚ) > 0 := by
  have := 0
  cancel_denoms

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h

example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring

example (h : 2 * (4 * a + d * 5 * b) ≠ (40 * c - 32 * a + b * 2 * 5 * d - 40 * b)) : a/5 + d*(b/4) ≠ c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  assumption

example (h : 27 ≤ (a + 3) ^ 3) : 1 ≤ (a / 3 + 1) ^ 3 := by
  cancel_denoms
  assumption

example (h : a > 2) : 1 < 2⁻¹ * a := by
  cancel_denoms
  assumption

example (h : 6 * b = a⁻¹ * 3 + c * 2): b = a⁻¹ * 2⁻¹ + c * 3⁻¹ := by
  cancel_denoms
  assumption

example (h : a * 5 + b * 6 = 30 * c) : a * 2⁻¹ * 3⁻¹ + b * 5⁻¹ = c := by
  cancel_denoms
  assumption

example (h : 5 * a^2 + 4 * b^3 = 0) : a ^ 2 / 4 + b ^ 3 / 5 = 0 := by
  cancel_denoms
  assumption

example (h : 5 * a^3 * b^2 = 72 * c) : (a/2)^3 * (b/3)^2 = c/5 := by
  cancel_denoms
  assumption

example (h: (5 * a ^ 3 + 8)^2 = 1600 * c) : ((a / 2) ^ 3 + 1/5)^2 = c := by
  cancel_denoms
  assumption

end

section
-- simulate the type of complex numbers
def C : Type := test_sorry
noncomputable instance : Field C := test_sorry
instance : CharZero C := test_sorry
variable (a b c d : C)
example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring
end
