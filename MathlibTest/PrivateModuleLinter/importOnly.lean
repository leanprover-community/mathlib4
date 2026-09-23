module

import Mathlib.Tactic.Linter.PrivateModule
import Mathlib.Logic.Basic

set_option linter.privateModule true

/- Should not fire, since the file has no declarations. -/
