import Mathlib.Tactic.DeprecateMe
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic

/--
info: * Pairings:
#[(`good_mul, aDeprecatable_mul), (`good_add, aDeprecatable_add)]

Try this:
/-- I also have a doc-string -/
@[to_additive "As do I"]
theorem good_mul : True :=
  .intro

@[deprecated (since := "YYYY-MM-DD")]
alias aDeprecatable_mul := good_mul

@[deprecated (since := "YYYY-MM-DD")]
alias aDeprecatable_add := good_add
-/
#guard_msgs in
deprecate to good_mul good_add "YYYY-MM-DD"
/-- I also have a doc-string -/
@[to_additive "As do I"]
theorem aDeprecatable_mul : True := .intro
