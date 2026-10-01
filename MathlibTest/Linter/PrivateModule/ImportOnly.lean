module

import Mathlib.Basic.Logic.Basic
import MathlibInit.Tactic.Linter.PrivateModule

set_option linter.privateModule true

/- Should not fire, since the file has no declarations. -/
