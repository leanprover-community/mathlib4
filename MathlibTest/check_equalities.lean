import Mathlib.Tactic.CheckEqualities

def N := Nat

/--
info: In equality
  1 = 1
the inferred type of the left hand side
1
is
  Nat
but should be
  N
---
warning: 'check_equalities' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : @Eq N (1 : Nat) (1 : Nat) := by
  #check_equalities
  change @Eq Nat _ _
  #check_equalities
  rfl
