/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Tactic.Measurability.Init
import Mathlib.Algebra.Group.Defs

/-!
# Measurability

We define the `measurability` tactic using `aesop`. -/

open Lean.Parser.Tactic (config)

attribute [aesop (rule_sets := [Measurable]) unfold norm] Function.comp
-- FIXME: `npowRec` is an internal implementation detail,
-- and `aesop` certainly should not know about it.
-- If anyone is working on the `measurability` tactic, please try to fix this!
attribute [aesop (rule_sets := [Measurable]) norm] npowRec

/--
The `measurability` attribute used to tag measurability statements for the `measurability` tactic.-/
macro "measurability" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Measurable):ident]))

/--
The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute. -/
macro "measurability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))

/--
The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success. -/
macro "measurability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))

-- Todo: implement `measurability!` and `measurability!?` and add configuration,
-- original syntax was (same for the missing `measurability` variants):
syntax (name := measurability!) "measurability!" (config)? : tactic
syntax (name := measurability!?) "measurability!?" (config)? : tactic
