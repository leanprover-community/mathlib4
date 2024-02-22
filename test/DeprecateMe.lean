import Mathlib.Tactic.DeprecateMe
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic

/--
info:
* New constants:
#[aDeprecatable_add, aDeprecatable_mul]

Try this:
/-- I also have a doc-string -/
  @[to_additive "As do I"]
  theorem aDeprecatable_mul : True :=
    .intro
  @[deprecated]
  alias aDeprecatable_add := good_mul
  @[deprecated]
  alias aDeprecatable_mul := good_add
-/
#guard_msgs in
deprecate to good_mul good_add
/-- I also have a doc-string -/
@[to_additive "As do I"]
theorem aDeprecatable_mul : True := .intro
