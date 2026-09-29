module
import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.AdaptationNote

example (h : 0 + 1 = 0) : False := by
  change 1 = 0 at h
  simp at h

example : 0 + 1 = 1 := by
  change 1 = 1
  rfl

/--
warning: Unused tactic linter: `change 1 = 1` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : 1 = 1 := by
  change 1 = 1
  rfl

set_option linter.defProp false in
def why2 : True → True := (by refine ·)

example : True := by
  #adaptation_note /-- hi -/
  exact .intro

-- both `;` and `<;>` are unseen by the linter
example : True ∧ True := by
  constructor <;> trivial;

set_option linter.unusedTactic true
/--
warning: Unused tactic linter: `congr` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
---
warning: Unused tactic linter: `done` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
-- the linter notices that `congr` is unused
example : True := by
  congr
  constructor
  done

/--
warning: Unused tactic linter: `show False` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : True := by
  show True -- `show` does not warn.
  guard_target = True -- `guard_target` also does not warn
  trivial <;> show False -- But, if it doesn't run at all, `show` does warn.

/--
warning: Unused tactic linter: `simp` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : True := by
  conv =>
    skip -- `skip` in `conv` mode does not warn.
    guard_target = True -- `guard_target` also does not warn
    simp -- other tactics in `conv` mode do warn
  trivial

example (a b : Nat) (h : a + 1 ≤ b + 1) : max a b ≤ b := by
  -- The linter does not look inside of dischargers, no matter whether it's actually used or not.
  have : True := by simp (disch := grind)
  simp (disch := grind) [Nat.max_eq_right]

section allowing_more_unused_tactics

/-- info: The `SyntaxNodeKind` is 'Lean.Parser.Tactic.refine'. -/
#guard_msgs in
#show_kind refine _

/-- info: The `SyntaxNodeKind` is 'Lean.Parser.Tactic.skip'. -/
#guard_msgs in
#show_kind skip

/--
error: Unknown constant `skip`
The command `#show_kind skip` may help to find the correct `SyntaxNodeKind`.
-/
#guard_msgs in
#allow_unused_tactic rfl skip

--  test that allowing more unused tactics has the desired effect of silencing the linter
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip

#guard_msgs in
example : True := by
  skip
  constructor
  done

end allowing_more_unused_tactics

section ignore_tactic_kind

syntax (name := doEmitWarningStx) "doEmitWarning" tactic : command
macro_rules
  | `(command| doEmitWarning $tac) => `(command| example : True := by $tac ; constructor)

syntax (name := doNotEmitWarningStx) "doNotEmitWarning" tactic : command
macro_rules
  | `(command| doNotEmitWarning $tac) => `(command| example : True := by $tac ; constructor)

-- `#eval` instead of `initialize` so that the effect can be tested in this file
#eval Mathlib.Linter.UnusedTactic.addIgnoreTacticKind ``doNotEmitWarningStx

/--
warning: Unused tactic linter: `congr` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in doEmitWarning congr

#guard_msgs in doNotEmitWarning congr

end ignore_tactic_kind
