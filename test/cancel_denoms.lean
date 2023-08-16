import Mathlib.Tactic.CancelDenoms
import Mathlib.Tactic.Ring

set_option autoImplicit true

section
variable {α : Type u} [LinearOrderedField α] (a b c d : α)

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

example (h : 40 * (4 * a + d * (5 * b)) ≠ 20 * (40 * c - 4 * (8 * a) + b * 2 * (5 * d) - 40 * b)) : a/5 + d*(b/4) ≠ c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  assumption

end

section
-- simulate the type of complex numbers
def C : Type := sorry
instance : Field C := sorry
instance : CharZero C := sorry
variable (a b c d : C)
example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring
end
