/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose
public import MathlibTest.Linter.SuperfluousExpose.Positive_TheoremOnly
public import MathlibTest.Linter.SuperfluousExpose.Positive_ClassOnly
public import MathlibTest.Linter.SuperfluousExpose.Positive_AbbrevOnly
public import MathlibTest.Linter.SuperfluousExpose.Positive_UnsafeDef
public import MathlibTest.Linter.SuperfluousExpose.Positive_PartialDef
public import MathlibTest.Linter.SuperfluousExpose.Positive_Notation
public import MathlibTest.Linter.SuperfluousExpose.Positive_Recursors
public import MathlibTest.Linter.SuperfluousExpose.Negative_PlainDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_IrreducibleDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_MatchPattern
public import MathlibTest.Linter.SuperfluousExpose.Negative_ToAdditive
public import MathlibTest.Linter.SuperfluousExpose.Negative_Inductive
public import MathlibTest.Linter.SuperfluousExpose.Negative_LocalInstance
public import MathlibTest.Linter.SuperfluousExpose.Negative_ScopedInstance
public import MathlibTest.Linter.SuperfluousExpose.Negative_NoExposeSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_ExposeInBlockComment
public import MathlibTest.Linter.SuperfluousExpose.Negative_ExposeOnNonPublicSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_InstPrefixedDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_TermPrefixedDef

/-! # Tests for the `superfluousExpose` linter

The linter fires at end-of-file when no declaration in the module benefits
from `@[expose]` exposure.

Positive cases (linter should FIRE):
* `Positive_TheoremOnly.lean`        — only `theorem`/`lemma`
* `Positive_ClassOnly.lean`          — `class` + instance
* `Positive_AbbrevOnly.lean`         — only `abbrev` (bodies auto-exposed)
* `Positive_UnsafeDef.lean`          — only `unsafe def` (kernel-opaque)
* `Positive_PartialDef.lean`         — only `partial def` (kernel-opaque)
* `Positive_Notation.lean`           — `notation`/`infix` only
* `Positive_Recursors.lean`          — `structure` (only auto-gen `.rec`/projections)

Negative cases (linter must NOT fire — exposure-relevant decl present):
* `Negative_PlainDef.lean`           — has a real plain `def`
* `Negative_IrreducibleDef.lean`     — `@[irreducible] def` / `irreducible_def`:
                                       downstream still uses `rw [name]`
* `Negative_MatchPattern.lean`       — `@[match_pattern]` def: pattern elaboration
                                       needs the body
* `Negative_ToAdditive.lean`         — `@[to_additive] def`: source AND twin are real defs
* `Negative_Inductive.lean`          — real `inductive` (not a structure)
* `Negative_LocalInstance.lean`      — `local instance` (conservative limitation)
* `Negative_ScopedInstance.lean`     — `scoped instance` (same limitation)
* `Negative_NoExposeSection.lean`    — no `@[expose] section` in source
* `Negative_ExposeInBlockComment.lean` — `@[expose] public section` appears only
                                       inside a `/- … -/` comment
* `Negative_ExposeOnNonPublicSection.lean` — `@[expose] section` (not `public`)
* `Negative_InstPrefixedDef.lean`    — `def inst<Capital>…` whose return type isn't a class
* `Negative_TermPrefixedDef.lean`    — `def term_…` whose return type isn't a parser descriptor
-/

-- A trivial decl to give this file a body (Lean's module system requires it).
private def superfluousExposeTestSuite : Unit := ()
