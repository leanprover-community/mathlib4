import Mathlib.Tactic.ClearExcept

set_option linter.unusedTactic false
set_option linter.unusedVariables false

-- Most basic test
example (_delete_this : Nat) (dont_delete_this : Int) : Nat := by
  clear * - dont_delete_this
  fail_if_success assumption
  exact dont_delete_this.toNat

-- Confirms that clearExcept does not delete class instances
example [dont_delete_this : Inhabited Nat] (dont_delete_this2 : Prop) : Inhabited Nat := by
  clear * - dont_delete_this2
  assumption

-- Confirms that clearExcept can clear hypotheses even when they have dependencies
example (delete_this : Nat) (_delete_this2 : delete_this = delete_this) (dont_delete_this : Int) :
    Nat := by
  clear * - dont_delete_this
  fail_if_success assumption
  exact dont_delete_this.toNat

-- Confirms that clearExcept does not clear hypotheses
-- when they have dependencies that should not be cleared
example (dont_delete_this : Nat) (dont_delete_this2 : dont_delete_this = dont_delete_this) :
    Nat := by
  clear * - dont_delete_this2
  exact dont_delete_this

-- Confirms that clearExcept can preserve multiple identifiers
example (_delete_this : Nat) (dont_delete_this : Int) (dont_delete_this2 : Int) : Nat := by
  clear * - dont_delete_this dont_delete_this2
  fail_if_success assumption
  exact dont_delete_this.toNat + dont_delete_this2.toNat
