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
---
warning: 'done' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
set_option linter.unusedTactic true in
-- the linter notices that `congr` is unused
example : True := by
  congr
  constructor
  done

section allowing_more_unused_tactics
--  test that allowing more unused tactics has the desired effect of silencing the linter
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip

#guard_msgs in
set_option linter.unusedTactic true in
example : True := by
  skip
  constructor
  done

end allowing_more_unused_tactics
