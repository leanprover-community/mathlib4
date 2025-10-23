import Mathlib.Tactic.DeprecateTo
import Mathlib.Tactic.ToAdditive

/--
info: * Pairings:
#[(new_name_mul, mul_easy_deprecated), (new_name_add, add_easy_deprecated)]

Try this:

  /-- I also have a doc-string -/
  @[to_additive /-- With its additive doc-string -/
      ]
  theorem new_name_mul : True :=
    .intro
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias mul_easy_deprecated := new_name_mul
  ⏎
  @[deprecated (since := "YYYY-MM-DD")]
  alias add_easy_deprecated := new_name_add
-/
#guard_msgs in
deprecate to new_name_mul new_name_add "YYYY-MM-DD"
/-- I also have a doc-string -/
@[to_additive /-- With its additive doc-string -/]
theorem mul_easy_deprecated : True := .intro
