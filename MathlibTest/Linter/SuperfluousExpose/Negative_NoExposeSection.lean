/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the content of the file would otherwise trigger the
linter, because it has only theorems and no def or inductive that benefits
from exposure. But the file contains no `@[expose] section`. The suggestion
to remove the `@[expose]` modifier does not apply, so the linter must stay
silent. -/

public section

namespace SuperfluousExposeTest.NoExposeSection

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.NoExposeSection
-- Expected: no linter warning. The file has no `@[expose] section`.
