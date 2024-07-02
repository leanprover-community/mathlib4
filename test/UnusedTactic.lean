import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.AdaptationNote

def why2 : True → True := (by refine ·)

example : True := by
  #adaptation_note /--hi-/
  exact .intro

-- both `;` and `<;>` are unseen by the linter
example : True ∧ True := by
  constructor <;> trivial;

set_option linter.unusedTactic false
/--
warning: 'congr' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
set_option linter.unusedTactic true in
-- the linter notices that `congr` is unused
example : True := by
  congr
  constructor
