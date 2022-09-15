import Mathlib.Tactic.Repeat

-- Verify that `repeat!` will skip over the `Type` goal that can not be solved by `constructor`,
-- and complete the `Unit` goal.
example : Type × Unit := by
  repeat! constructor
  exact Nat

-- Verify that `repeat1!` only succeeds if the tactic succeeds on the main goal.
example : Type := by
  fail_if_success repeat1! constructor
  exact Nat
