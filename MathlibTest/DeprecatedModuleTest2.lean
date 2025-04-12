import MathlibTest.DeprecatedModule

/--
warning: 'MathlibTest.DeprecatedModule' has been deprecated: please replace this import by

import Mathlib.Tactic.Linter.DeprecatedModule
import Mathlib.Tactic.Basic

note: this linter can be disabled with `set_option linter.deprecated.module false`
-/
#guard_msgs in
/-!
This file imports a deprecated module.
-/
