import Mathlib.Tactic.MultigoalsLinter
import Mathlib.Tactic.Conv

set_option linter.multiGoal false in
set_option linter.multiGoal true in
/--
warning: 'exact .intro' leaves 1 goal 'Lean.Parser.Tactic.exact' [linter.multiGoal]
-/
#guard_msgs in
example : True := by
  by_cases 0 = 0
  exact .intro
  exact .intro

set_option linter.multiGoal false in
set_option linter.multiGoal true in
/--
warning: 'assumption' leaves 1 goal 'Lean.Parser.Tactic.assumption' [linter.multiGoal]
-/
-- the linter keeps linting after ignoring a `conv`, `conv_lhs`, `conv_rhs`
#guard_msgs in
example {n : Nat} (hn : n = 0) : n + 0 = 0 := by
  conv =>
    congr
    rw [← Nat.add_zero 0]
  conv_lhs =>
    congr
    rw [← Nat.add_zero n]
    rfl
  conv_rhs =>
    rw [← Nat.add_zero 0]
    congr
    rfl
    rfl
  by_cases 0 = 0
  assumption
  assumption

set_option linter.multiGoal false in
set_option linter.multiGoal true in
/--
warning: 'rfl' leaves 1 goal 'Lean.Parser.Tactic.tacticRfl' [linter.multiGoal]
-/
-- the linter allows `iterate` and `repeat'`, but continues to lint.
#guard_msgs in
example (p : Prop) (hp : p) : (0 = 0 ∧ p) ∨ 0 = 0 := by
  iterate left; decide
  repeat' left; decide
  refine Or.inl ⟨?_, ?_⟩
  rfl
  assumption

example (p : Bool) : 0 = 0 := by
  cases p
  case' false => rfl
  case' true => rfl
