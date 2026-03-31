-- This file tests that `import all` of a deprecated module produces warnings.
-- Core Lean 4 generates deprecation warnings at import time.
module

import all MathlibTest.DeprecatedModuleNew

/-!
This file imports a deprecated module with `import all`.
-/
