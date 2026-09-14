/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the text `@[expose] public section` appears on its own
line inside the block comment below, and the file opens a plain
`public section`. The linter reads the elaborated scope, not the source
text, so it must not fire. -/

/-
@[expose] public section
-/

public section

namespace SuperfluousExposeTest.ExposeInBlockComment

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeInBlockComment

end
