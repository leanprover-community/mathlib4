/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: an `@[expose] section` nested inside a `public section`. The inner scope
inherits `isPublic`, so the linter treats the inner section as an exposed region and points the
warning at its header. The linter must fire. -/

public section

@[expose] section

namespace SuperfluousExposeTest.NestedExposeSection

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.NestedExposeSection

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end

end
