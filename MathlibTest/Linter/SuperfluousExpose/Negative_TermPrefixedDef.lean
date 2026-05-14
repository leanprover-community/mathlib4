/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: regular `def`s whose name starts with `term` (with or without
a trailing underscore) but which are not notation-generated. The leaf-name
heuristic alone would match these; the type-level guard (return type must be
`Lean.ParserDescr` / `TrailingParserDescr` / `Macro`) prevents the false
positive. We test both `term_<snake>` and `term<Camel>` shapes because notation
generates either depending on the operator's syntax — see the implementation
notes in `SuperfluousExpose.lean` for details. -/

@[expose] public section

namespace SuperfluousExposeTest.TermPrefixedDef

-- Snake-cased: matches the `term_` prefix; type gate rescues.
def term_helper : Nat := 42

theorem term_helper_eq : term_helper = 42 := rfl

-- Camel-cased: matches the broader `term` prefix (no underscore) introduced
-- to cover function-like notation generators like `«termF(_)»`. Type gate
-- still rescues.
def termHelperCamel : Nat := 7

theorem term_helper_camel_eq : termHelperCamel = 7 := rfl

end SuperfluousExposeTest.TermPrefixedDef
-- Expected: NO linter warning.
