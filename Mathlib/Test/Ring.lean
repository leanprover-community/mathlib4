import Mathlib.Tactic.Ring

-- Causes `PANIC at Lean.Expr.getRevArg! Lean.Expr:508:22: invalid index`:
example (A : ℕ) : (2 * A) ^ 2 = (2 * A) ^ 2 := by ring
