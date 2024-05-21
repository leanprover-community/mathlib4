import Mathlib.Tactic

example {n : Nat} (hn : n = 0) : (n = 0) ∧ (n = 0) := by
  constructor
  simp_rw [hn,hn]  -- does this work?
