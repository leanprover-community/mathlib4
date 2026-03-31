-- This file tests that `meta import` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module

meta import MathlibTest.DeprecatedModuleNew

/-!
This file imports a deprecated module with `meta import`.
-/
