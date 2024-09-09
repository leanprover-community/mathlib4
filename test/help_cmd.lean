import Mathlib.Tactic.HelpCmd
#guard_msgs(error, drop info) in
#help tactic
def foo := 1

/--
info: syntax "#check"... [Lean.Parser.Command.check]

syntax "#check_failure"... [Lean.Parser.Command.check_failure]

syntax "#check_simp"... [Lean.Parser.checkSimp]
  `#check_simp t ~> r` checks `simp` reduces `t` to `r`.

syntax "#check_simp"... [Lean.Parser.checkSimpFailure]
  `#check_simp t !~>` checks `simp` fails on reducing `t`.

syntax "#check_tactic"... [Lean.Parser.checkTactic]
  `#check_tactic t ~> r by commands` runs the tactic sequence `commands`
  on a goal with `t` and sees if the resulting expression has reduced it
  to `r`.

syntax "#check_tactic_failure"... [Lean.Parser.checkTacticFailure]
  `#check_tactic_failure t by tac` runs the tactic `tac`
  on a goal with `t` and verifies it fails.
-/
#guard_msgs in
#help command "#chec"
