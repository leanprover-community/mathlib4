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
public import MathlibTest.Linter.SuperfluousExpose.Positive_Structure
public import MathlibTest.Linter.SuperfluousExpose.Positive_PartialDef
public import MathlibTest.Linter.SuperfluousExpose.Positive_NoExposeDef
public import MathlibTest.Linter.SuperfluousExpose.Positive_Notation
public import MathlibTest.Linter.SuperfluousExpose.Positive_ScopedLocalInstance
public import MathlibTest.Linter.SuperfluousExpose.Positive_NestedExposeSection
public import MathlibTest.Linter.SuperfluousExpose.Positive_MultiSection
public import MathlibTest.Linter.SuperfluousExpose.Positive_FileEndClose
public import MathlibTest.Linter.SuperfluousExpose.Negative_PlainDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_UnsafeDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_IrreducibleDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_ReducibleDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_ToAdditive
public import MathlibTest.Linter.SuperfluousExpose.Negative_InstanceAttrDef
public import MathlibTest.Linter.SuperfluousExpose.Negative_DerivingDecidableEq
public import MathlibTest.Linter.SuperfluousExpose.Negative_NoExposeSection
public import MathlibTest.Linter.SuperfluousExpose.Negative_ExposeOnNonPublicSection

/-! # Tests for the `superfluousExpose` linter

The linter reports each `@[expose] public section` where no declaration benefits from exposure.
The warning fires when the section closes: at its `end` command, or at the terminal command when
the end of the file closes the section. Each file tests one case, and every file turns the option
on at the top.

A `Positive_*` file states the expected warning with `#guard_msgs in end`, which captures the
verdict of the section that the `end` closes. An empty expectation there asserts silence for one
section of the file. `Positive_FileEndClose.lean` uses `#guard_msgs in #exit`: `#exit` is a
terminal command, so the linter settles the open section there, and the expectation starts with
`warning: using 'exit' to interrupt Lean`.

A `Negative_*` file produces no output. CI runs `lake --iofail test`, so a warning from such a
file fails the build. -/
