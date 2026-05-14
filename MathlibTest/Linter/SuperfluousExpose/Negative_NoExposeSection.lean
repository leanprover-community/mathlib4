/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file's content would otherwise trigger the linter
(theorem-only, no `def`/`inductive` benefiting from exposure), but the source
text does **not** contain `@[expose] section`. The suggestion to "remove
the `@[expose]` modifier" wouldn't apply, so the linter must stay silent. -/

public section

namespace SuperfluousExposeTest.NoExposeSection

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.NoExposeSection
-- Expected: NO linter warning (no `@[expose] section` in source).
