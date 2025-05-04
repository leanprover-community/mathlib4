import Mathlib.Tactic.Linter.Lint

/--
warning: use 'intro a' instead.
note: this linter can be disabled with `set_option linter.introsVar false`
-/
#guard_msgs in
example : ∀ a b c : Nat, a + b = c → a + b = c := by
  intros a
  intro b c
  exact id
