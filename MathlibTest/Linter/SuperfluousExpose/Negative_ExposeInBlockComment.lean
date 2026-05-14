/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-
A multi-line block comment that mentions, on its own line:
@[expose] public section
which must NOT be picked up by the linter's source scanner.
-/

public section

namespace SuperfluousExposeTest.ExposeInBlockComment

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeInBlockComment

end
-- Expected: NO linter warning (the `@[expose] public section` appears only
-- inside a block comment, not as a real header).
