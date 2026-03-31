-- This file tests that `public import` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module

public import MathlibTest.DeprecatedModuleNew

/-!
This file imports a deprecated module with `public import`.
-/
