import Mathlib.Tactic.Linter.DeprecatedModule
import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Linter.DocString

deprecated_module (since := "2025-04-10")

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with no message
-/
#guard_msgs in
#show_deprecated_modules

-- Deprecating the current module is possible and allows to add more deprecation information.
deprecated_module "We can also give more details about the deprecation" (since := "2025-04-10")

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'We can also give more details about the deprecation'

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with no message
-/
#guard_msgs in
#show_deprecated_modules

/- Commenting out the following test, since it does not work in CI
besides, it suggests the current date, so it should *not* be uncommented
until that is also fixed!
/-- error: Invalid date: the expected format is "2025-04-14" -/
#guard_msgs in
deprecated_module "Text" (since := "2025-02-31")
-/

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'We can also give more details about the deprecation'

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with no message
-/
#guard_msgs in
#show_deprecated_modules
