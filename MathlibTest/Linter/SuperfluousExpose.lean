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

The linter fires at the end of a file when no declaration in the module
benefits from `@[expose]` exposure.

Positive cases, where the linter must fire:
* `Positive_TheoremOnly.lean`: only theorems.
* `Positive_ClassOnly.lean`: a class and an instance.
* `Positive_AbbrevOnly.lean`: only abbrevs, whose bodies are exposed by default.
* `Positive_UnsafeDef.lean`: only an `unsafe def`, which is opaque to the kernel.
* `Positive_PartialDef.lean`: only a `partial def`, which is opaque to the kernel.
* `Positive_Notation.lean`: only `notation`.
* `Positive_Recursors.lean`: a structure, which yields only auto-generated constants.

Negative cases, where the linter must not fire:
* `Negative_PlainDef.lean`: a plain `def`.
* `Negative_IrreducibleDef.lean`: `@[irreducible] def`; downstream code can still use `rw`.
* `Negative_MatchPattern.lean`: a `@[match_pattern]` def; pattern elaboration needs the body.
* `Negative_ToAdditive.lean`: a `@[to_additive]` def; the source and the twin are real defs.
* `Negative_Inductive.lean`: an inductive that is not a structure.
* `Negative_LocalInstance.lean`: a `local instance`, a conservative limitation.
* `Negative_ScopedInstance.lean`: a `scoped instance`, the same limitation.
* `Negative_NoExposeSection.lean`: no `@[expose] section` in the file.
* `Negative_ExposeInBlockComment.lean`: `@[expose] public section` only inside a comment.
* `Negative_ExposeOnNonPublicSection.lean`: `@[expose] section` without `public`.
* `Negative_InstPrefixedDef.lean`: a def named `inst<Capital>…` whose type is not a class.
* `Negative_TermPrefixedDef.lean`: a def named `term…` whose type is not a parser descriptor.
-/

-- A trivial decl to give this file a body (Lean's module system requires it).
private def superfluousExposeTestSuite : Unit := ()
