import Mathlib.Tactic.IrreducibleDef

/-- Add two natural numbers, but not during unification. -/
irreducible_def frobnicate (a b : Nat) :=
  a + b

example : frobnicate a 0 = a := by
  simp [frobnicate_def]

irreducible_def justAsArbitrary [Inhabited α] : α :=
  default

irreducible_def withoutType := 42

irreducible_def withEquations : Nat → Nat
  | 0 => 42
  | (n+1) => 314

irreducible_def withUniv.{u, v} := (Type v, Type u)
example : withUniv.{u, v} = (Type v, Type u) := by rw [withUniv_def]
