-- This file tests that a plain `import` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module --deprecated_module: ignore

import MathlibTest.Linter.DeprecatedModule.ImportBase

/-!
This file imports a deprecated module with a plain `import`.
-/

/--
info: Deprecated modules

'MathlibTest.Linter.DeprecatedModule.ImportBase' deprecates to
#[Mathlib.Tactic.Linter.DocPrime, Mathlib.Tactic.Linter.DocString]
with message 'Testing public import deprecation'
-/
#guard_msgs in
#show_deprecated_modules
