-- This file tests that `import all` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module

import all MathlibTest.DeprecatedModuleNew -- deprecated_module: ignore

/-!
This file imports a deprecated module with `import all`.
-/


/--
info: Deprecated modules

'MathlibTest.DeprecatedModuleNew' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'Testing public import deprecation'
-/
#guard_msgs in
#show_deprecated_modules
