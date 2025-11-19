module

import Mathlib.Tactic.Linter.PrivateModule

-- Should not fire, since `foo` is `public`.

public theorem foo : True := trivial
