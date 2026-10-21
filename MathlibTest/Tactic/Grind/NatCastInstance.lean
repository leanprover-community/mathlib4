module

public import Mathlib.Data.ENat.Monoid

@[expose] public section

example : (Lean.Grind.Semiring.natCast : NatCast ℕ∞) = ENat.instNatCast := by
  with_reducible_and_instances rfl
