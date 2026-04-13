-- This file tests that `public import` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module --deprecated_module: ignore

public import MathlibTest.DeprecatedModuleNew

/-!
This file imports a deprecated module with `public import`.
-/

/--
info: Deprecated modules

'MathlibTest.DeprecatedModuleNew' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'Testing public import deprecation'
-/
#guard_msgs in
#show_deprecated_modules
