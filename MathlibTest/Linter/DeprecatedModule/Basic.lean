import MathlibInit.Tactic.Linter.DocPrime
import MathlibInit.Tactic.Linter.DocString

deprecated_module (since := "2025-04-10")

/--
info: Deprecated modules

'MathlibTest.Linter.DeprecatedModule.Basic' deprecates to
#[MathlibInit.Tactic.Linter.DocPrime, MathlibInit.Tactic.Linter.DocString]
with no message
-/
#guard_msgs in
#show_deprecated_modules

/--
warning: module is already marked as deprecated
-/
#guard_msgs in
-- Deprecating the current module is possible and replaces previous deprecation information.
deprecated_module "We can also give more details about the deprecation" (since := "2025-04-10")

/--
info: Deprecated modules

'MathlibTest.Linter.DeprecatedModule.Basic' deprecates to
#[MathlibInit.Tactic.Linter.DocPrime, MathlibInit.Tactic.Linter.DocString]
with message 'We can also give more details about the deprecation'
-/
#guard_msgs in
#show_deprecated_modules
