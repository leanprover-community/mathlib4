import Lean.Elab.Declaration
import Mathlib.Util.SuppressSorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := sorry

section

set_option suppressSorry true

#guard_msgs in example : True := sorry

#guard_msgs in inductive Foo (x : sorry) : Prop

#guard_msgs in structure Bar (x : sorry) : Prop

#guard_msgs in variable (x : sorry)
#guard_msgs in def y := ((sorry : Nat), x)

elab "#elab_that_skips_elabCommand" cmd:command : command =>
  Lean.Elab.Command.elabDeclaration cmd

#guard_msgs in #elab_that_skips_elabCommand example : True := sorry

end

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := sorry
