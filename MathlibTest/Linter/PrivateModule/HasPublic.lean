module

import Mathlib.Tactic.Linter.PrivateModule

set_option linter.privateModule true

-- Should not fire, since `foo` is `public`.

public theorem foo : True := trivial
