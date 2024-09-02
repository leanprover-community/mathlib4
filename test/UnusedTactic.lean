import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Linter.UnnecessaryTactic
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
elab "no " _tac:tactic : tactic => return

set_option linter.unnecessaryTactic false

/--
warning: 'Lean.Parser.Tactic.skip, (2098, 4)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
---
warning: 'tacticNo_, (2061, 47)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
-/
#guard_msgs in
set_option linter.unnecessaryTactic true in
set_option linter.unusedTactic true in
example : True := by
  no (
    #adaptation_note /-- -/
    skip
    )
  exact .intro

/--
warning: 'Lean.Parser.Tactic.skip, (2098, 4)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
---
warning: 'tacticNo_, (2061, 47)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
-/
#guard_msgs in
set_option linter.unnecessaryTactic true in
set_option linter.unusedTactic true in
example : True := by
  no (
    skip
    )
  exact .intro


-- test that even with the extra infotrees arising from `set_option`
-- the linter works correctly
set_option linter.unusedTactic false in
#guard_msgs in
set_option linter.unnecessaryTactic true in
theorem X : True ∧ True := by
  constructor
  exact .intro
  exact .intro

#guard_msgs in
set_option linter.unnecessaryTactic true in
-- check that `binderTactic`s are ignored
variable (n : Nat := by intros; exact 0)

/--
warning: 'Lean.Parser.Tactic.done, (2983, 4)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
---
warning: 'Lean.Parser.Tactic.skip, (2991, 4)' is unnecessary.
note: this linter can be disabled with `set_option linter.unnecessaryTactic false`
-/
#guard_msgs in
set_option linter.unnecessaryTactic true in
example (h : False) : 0 = 0 ∧ False:= by
  constructor <;>
    try (exact h; done)
  skip
  trivial

set_option linter.unnecessaryTactic true in
-- syntax quotations are ignored
run_cmd
  let _ ← `(tactic| (intros; intros))
