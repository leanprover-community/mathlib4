import MathlibTest.DeprecatedModule --deprecated_module: ignore

/-!
This file imports a deprecated module.
-/

/--
info: Deprecated modules

'MathlibTest.DeprecatedModule' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'We can also give more details about the deprecation'
-/
#guard_msgs in
#show_deprecated_modules
