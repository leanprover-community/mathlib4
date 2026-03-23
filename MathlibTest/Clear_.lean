import Mathlib.Tactic.Clear_
import Mathlib.Tactic.Replace

set_option linter.unusedTactic false

-- Most basic test
example (_delete_this : Nat) : Nat := by
  clear_
  fail_if_success assumption
  exact 0

-- Confirms that clear_ does not delete class instances
example [_dont_delete_this : Inhabited Nat] : Inhabited Nat := by
  clear_
  assumption

-- Confirms that clear_ clears _delete_this but not dont_delete_this
example (_delete_this : Nat) (dont_delete_this : Int) : Nat := by
  clear_
  fail_if_success assumption
  exact dont_delete_this.toNat

-- Confirms that clear_ can clear hypotheses even when they have dependencies
example (_delete_this : Type) (_delete_this_dep : _delete_this)
    (_delete_this_rw : _delete_this = Nat)
    (_delete_this_dep_dep : _delete_this_dep = _delete_this_dep) : Nat := by
  clear_
  fail_if_success
    rw [← _delete_this_rw]
  exact 0

-- Confirms that clear_ does not clear hypotheses
-- when they have dependencies that should not be cleared
example (_dont_delete_this : Type) (dep : _dont_delete_this) : _dont_delete_this := by
  clear_
  assumption

-- Confirms that clear_ does not break the goal
example (_dont_delete_this : Type) : _dont_delete_this = _dont_delete_this := by
  clear_
  rfl

-- Confirms that clear_ clears all that it can even if some underscored hypotheses cannot be cleared
example (_dont_delete_this : Type) (_delete_this : _dont_delete_this = _dont_delete_this) :
  _dont_delete_this = _dont_delete_this := by
  clear_
  fail_if_success assumption
  rfl
