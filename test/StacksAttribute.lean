import Mathlib.Tactic.StacksAttribute

/-- warning: Spaces are not allowed in '044 Q ' -/
#guard_msgs in
@[stacks 044 Q "", stacks A044Q "A comment", stacks A044Q ]
example : True := .intro
