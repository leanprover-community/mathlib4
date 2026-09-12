module

public import Mathlib.Tactic.Linter.HaveILetI

/--
warning: Try this: ⏎
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
---
warning: Try this: ⏎
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : True := trivial
  letI : True := trivial
  trivial
