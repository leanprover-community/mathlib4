import Mathlib.Tactic.Classical
import Std.Tactic.GuardExpr

noncomputable def foo : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  classical!
  have := ∀ p, decide p -- uses the classical instance
  -- uses the classical instance even though `0 < 1` is decidable
  guard_expr decide (0 < 1) = @decide (0 < 1) (‹(a : Prop) → Decidable a› _)
  exact decide (0 < 1)

def bar : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  classical
  have := ∀ p, decide p -- uses the classical instance
  guard_expr decide (0 < 1) = @decide (0 < 1) (Nat.decLt 0 1)
  exact decide (0 < 1) -- uses the decidable instance

-- double check no leakage
def bar' : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  exact decide (0 < 1) -- uses the decidable instance
