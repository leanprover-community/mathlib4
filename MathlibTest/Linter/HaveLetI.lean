module

public import Mathlib.Tactic.Linter.HaveLetI

/--
warning: Try this: ⏎
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.
---
warning: Try this: ⏎
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.
-/
#guard_msgs in
example : True := by
  haveI : True := trivial
  letI : True := trivial
  trivial
