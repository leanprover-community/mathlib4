import MathlibTest.DeprecatedModuleTest1

/--
warning: 'MathlibTest.DeprecatedModuleTest1' has been deprecated: please replace this import by

import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule

note: this linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module.
-/
