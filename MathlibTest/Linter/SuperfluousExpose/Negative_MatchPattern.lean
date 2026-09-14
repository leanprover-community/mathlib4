/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a `@[match_pattern]` def. The attribute lets a `match`
expression use the def as a pattern, as in `match x with | mkPat a => ...`,
and that elaboration step reads the body. A companion `@[reducible]`
attribute makes no difference. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.MatchPattern

@[match_pattern, simp, reducible]
def trivialPattern : Bool := true

theorem trivialPattern_eq : trivialPattern = true := rfl

end SuperfluousExposeTest.MatchPattern
