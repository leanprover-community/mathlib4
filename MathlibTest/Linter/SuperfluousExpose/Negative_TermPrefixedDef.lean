/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: plain `def`s whose names start with `term` and that do
not come from notation. The linter treats a def as a parser entry only when
the leaf name matches and the return type is `Lean.ParserDescr`,
`TrailingParserDescr` or `Macro`, so the type check keeps these two defs
classified as defs. Notation generates both the `term_<snake>` and the
`term<Camel>` shape, so both appear here. The implementation notes in
`SuperfluousExpose.lean` cover the prefix. -/

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
