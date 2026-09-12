/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file uses `@[expose] section` without `public`. The
section has no downstream visibility, so `@[expose]` has no effect there,
and its removal changes nothing downstream. The linter must not fire: its
suggestion applies to `public section`s only. -/

@[expose] section

namespace SuperfluousExposeTest.ExposeOnNonPublic

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeOnNonPublic

end
-- Expected: no linter warning. The `@[expose]` is on a non-public section.
