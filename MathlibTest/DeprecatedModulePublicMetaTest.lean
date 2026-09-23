module

public meta import MathlibTest.DeprecatedModuleNew

/--
warning: Testing public import deprecation
'MathlibTest.DeprecatedModuleNew' has been deprecated: please replace this import by

import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Linter.DocString


Note: This linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module with `public meta import`.
-/
