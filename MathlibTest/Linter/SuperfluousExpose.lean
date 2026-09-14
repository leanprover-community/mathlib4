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
public import MathlibTest.Linter.SuperfluousExpose.Positive_Inductive
public import MathlibTest.Linter.SuperfluousExpose.Positive_PartialDef
public import MathlibTest.Linter.SuperfluousExpose.Positive_Notation
public import MathlibTest.Linter.SuperfluousExpose.Positive_Recursors
public import MathlibTest.Linter.SuperfluousExpose.Positive_LocalInstance
public import MathlibTest.Linter.SuperfluousExpose.Positive_ScopedInstance
public import MathlibTest.Linter.SuperfluousExpose.Positive_MultiSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_PlainDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_UnsafeDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_IrreducibleDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_ReducibleDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_MatchPattern
public import MathlibTest.Linter.SuperfluousExpose.Negative_ToAdditive
public import MathlibTest.Linter.SuperfluousExpose.Negative_NoExposeSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_ExposeInBlockComment
public import MathlibTest.Linter.SuperfluousExpose.Negative_ExposeOnNonPublicSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_InstPrefixedDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_InstanceAttrDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_TermPrefixedDef

/-! # Tests for the `superfluousExpose` linter

The linter reports each `@[expose] public section` that contains no
declaration whose body must be visible downstream. The warning fires when
the section closes: at its `end` command, or at the terminal command for a
section that the end of the file closes. One case gets one file.

## How a test captures the warning

A positive file states its expectation with `#guard_msgs`. Two shapes appear,
one per kind of close:

* `#guard_msgs in end` captures the verdict of the section that the `end`
  closes. `Positive_MultiSection.lean` uses this shape, and an empty
  expectation there asserts silence for one section of the file.
* `set_option linter.superfluousExpose true in #guard_msgs in #exit`
  captures the verdict of a section that the end of the file closes. `#exit`
  is a terminal command, so the linter settles the section there and clears
  it. The expected block starts with `warning: using 'exit' to interrupt
  Lean`.

A negative file needs no `#guard_msgs`. It turns the option on at the top and
produces no output. CI runs `lake --iofail test`, so a warning from any of
these files fails the build.

## Positive cases, where the linter must fire

* `Positive_TheoremOnly.lean`: only theorems.
* `Positive_ClassOnly.lean`: a class and an instance.
* `Positive_AbbrevOnly.lean`: only abbrevs, which carry their own exposure.
* `Positive_Inductive.lean`: an inductive, which the modifier does not reach.
* `Positive_PartialDef.lean`: a `partial def`, which is opaque to the kernel.
* `Positive_Notation.lean`: only `notation`.
* `Positive_Recursors.lean`: a structure, which yields only generated constants.
* `Positive_LocalInstance.lean`: a `local instance`, classified while it is active.
* `Positive_ScopedInstance.lean`: a `scoped instance`, classified while it is active.
* `Positive_MultiSection.lean`: three sections, each with its own verdict.

## Negative cases, where the linter must stay silent

* `Negative_PlainDef.lean`: a plain `def`.
* `Negative_UnsafeDef.lean`: an `unsafe def`; downstream `unsafe` code uses `rfl`.
* `Negative_IrreducibleDef.lean`: `@[irreducible] def`; downstream code uses `rw`.
* `Negative_ReducibleDef.lean`: `@[reducible] def`; only `abbrev` carries its own exposure.
* `Negative_MatchPattern.lean`: a `@[match_pattern]` def; pattern elaboration reads the body.
* `Negative_ToAdditive.lean`: a `@[to_additive]` def; the source and the twin are both defs.
* `Negative_NoExposeSection.lean`: no `@[expose] section` in the file.
* `Negative_ExposeInBlockComment.lean`: `@[expose] public section` only inside a comment.
* `Negative_ExposeOnNonPublicSection.lean`: `@[expose] section` without `public`.
* `Negative_InstPrefixedDef.lean`: a def named `inst<Capital>…` whose type is not a class.
* `Negative_InstanceAttrDef.lean`: a `def` with `@[instance]`, which keeps the def rules.
* `Negative_TermPrefixedDef.lean`: a def named `term…` whose type is not a parser descriptor.
-/

-- A trivial decl to give this file a body (Lean's module system requires it).
private def superfluousExposeTestSuite : Unit := ()
