/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file uses `@[expose] section` (without `public`).
That's not a downstream-visibility section, so `@[expose]` is meaningless
there and removing it accomplishes nothing observable downstream. The
linter must NOT fire — its suggestion is targeted at `public section`s
only. -/

@[expose] section

namespace SuperfluousExposeTest.ExposeOnNonPublic

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeOnNonPublic

end
-- Expected: NO linter warning (the `@[expose]` is on a non-public section).
