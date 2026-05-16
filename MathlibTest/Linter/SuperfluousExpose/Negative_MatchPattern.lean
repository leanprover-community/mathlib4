/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: `@[match_pattern]` `def`. The `@[match_pattern]` attribute
makes the definition usable as a pattern (e.g. `match x with | mkPat a => ...`).
That elaboration step needs the body exposed regardless of any `@[reducible]`
companion attribute. Linter must NOT fire. -/

@[expose] public section

namespace SuperfluousExposeTest.MatchPattern

@[match_pattern, simp, reducible]
def trivialPattern : Bool := true

theorem trivialPattern_eq : trivialPattern = true := rfl

end SuperfluousExposeTest.MatchPattern
-- Expected: NO linter warning.
