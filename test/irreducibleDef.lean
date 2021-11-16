import Mathlib.Tactic.IrreducibleDef

/-- Add two natural numbers, but not during unification. -/
irreducible_def frobnicate (a b : Nat) :=
  a + b

example : frobnicate a 0 = a := by
  simp [frobnicate_def]

irreducible_def justAsArbitrary [Inhabited α] : α :=
  arbitrary
