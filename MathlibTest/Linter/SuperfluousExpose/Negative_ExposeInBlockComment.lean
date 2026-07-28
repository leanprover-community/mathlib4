/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-
This block comment contains, on its own line:
@[expose] public section
This text must not trigger the linter. Only an elaborated section scope
counts.
-/

public section

namespace SuperfluousExposeTest.ExposeInBlockComment

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ExposeInBlockComment

end
-- Expected: no linter warning. The `@[expose] public section` text appears
-- only inside a block comment, not as a real header.
