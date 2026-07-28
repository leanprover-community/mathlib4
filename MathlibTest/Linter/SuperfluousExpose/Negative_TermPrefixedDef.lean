/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: regular `def`s whose names start with `term`, with or
without a trailing underscore, and that do not come from notation. The
leaf-name check alone would match them. The type check prevents the false
positive: the return type must be `Lean.ParserDescr`, `TrailingParserDescr`,
or `Macro`. We test both the `term_<snake>` shape and the `term<Camel>`
shape, because notation generates either shape, dependent on the syntax of
the operator. See the implementation notes in `SuperfluousExpose.lean`. -/

@[expose] public section

namespace SuperfluousExposeTest.TermPrefixedDef

-- The snake-cased name matches the `term_` prefix. The type check rescues it.
def term_helper : Nat := 42

theorem term_helper_eq : term_helper = 42 := rfl

-- The camel-cased name matches the broader `term` prefix, which covers
-- function-like notation names such as `«termF(_)»`. The type check rescues
-- it.
def termHelperCamel : Nat := 7

theorem term_helper_camel_eq : termHelperCamel = 7 := rfl

end SuperfluousExposeTest.TermPrefixedDef
-- Expected: no linter warning.
