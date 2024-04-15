import Mathlib.Tactic.UnusedTactic

#guard_msgs in
example : ∀ x : Nat, x = x := (by induction · <;> rfl; )

#guard_msgs in
example : ∀ _x : Nat, True := fun _x => by
  rw [← Classical.not_not (a := True)]
  · trivial

set_option linter.unusedTactic false in
set_option linter.unusedTactic true in
/--
warning: 'skip' tactic does nothing [linter.unusedTactic]
---
warning: 'congr' tactic does nothing [linter.unusedTactic]
---
warning: 'done' tactic does nothing [linter.unusedTactic]
-/
#guard_msgs in
example : ∀ _x : Nat, True := fun _x => by
  skip
  congr
  exact .intro
  done
