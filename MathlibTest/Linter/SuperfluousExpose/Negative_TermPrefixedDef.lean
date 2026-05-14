/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a regular `def` whose name starts with `term_` but is not
notation-generated. The leaf-name heuristic alone would match this; the
type-level guard (return type must be `Lean.ParserDescr` / `TrailingParserDescr`
/ `Macro`) prevents the false positive. -/

@[expose] public section

namespace SuperfluousExposeTest.TermPrefixedDef

def term_helper : Nat := 42

theorem term_helper_eq : term_helper = 42 := rfl

end SuperfluousExposeTest.TermPrefixedDef
-- Expected: NO linter warning.
