/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: only theorems, so the content alone would trigger the
linter. The file opens a plain `public section` and carries no `@[expose]`
modifier to remove, so the linter must not fire. -/

public section

namespace SuperfluousExposeTest.NoExposeSection

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.NoExposeSection
