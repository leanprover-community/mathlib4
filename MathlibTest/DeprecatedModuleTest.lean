import MathlibTest.DeprecatedModule

/--
warning: We can also give more details about the deprecation
'MathlibTest.DeprecatedModule' has been deprecated: please replace this import by

import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Linter.DocString


Note: This linter can be disabled with `set_option linter.deprecated.module false`
---
warning:
'MathlibTest.DeprecatedModule' has been deprecated: please replace this import by

import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Linter.DocString


Note: This linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module.
-/
