import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.AdaptationNote
import Mathlib.adomaniLeanUtils.inspect_syntax

open Lean hiding Rat
open Elab Meta Term

syntax normStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"
syntax (name := linearCombination) "linear_combination"
  (normStx)? (ppSpace colGt term)? : tactic

elab_rules : tactic
  | `(tactic| linear_combination $[(norm := $tac)]?) => Tactic.withMainContext do
    Lean.Elab.Tactic.evalTactic (← `(tactic|rfl))

def why2 : True → True := (by refine ·)

inspect
example : 0 = 0 := by
  --skip
  linear_combination (norm := skip)
  --rfl

example : True := by
  #adaptation_note /-- hi -/
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
