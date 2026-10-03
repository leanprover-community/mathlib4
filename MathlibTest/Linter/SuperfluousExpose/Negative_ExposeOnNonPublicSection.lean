/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: `@[expose] section` without `public`. Only a
`public section` has downstream visibility, so the modifier has no effect
here. The suggestion applies to a `public section`, so the linter must not
fire. -/

@[expose] section

namespace SuperfluousExposeTest.ExposeOnNonPublic

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeOnNonPublic

end
