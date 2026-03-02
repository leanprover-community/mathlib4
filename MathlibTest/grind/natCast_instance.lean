import Mathlib.Data.ENat.Basic

example : (Lean.Grind.Semiring.natCast : NatCast ℕ∞) = ENat.instNatCast := by
  with_reducible_and_instances rfl
