/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Tactic.FunProp.Decl
public import Mathlib.Tactic.Measurability.Init

/-!
# Measurability

We define the `measurability` tactic using `aesop`. -/

public meta section

open Lean
open Lean.Meta (MetaM)
open Lean.Parser.Tactic (optConfig)
open Mathlib.Meta.FunProp (isFunPropGoal)

/--
The `measurability` attribute used to tag measurability statements for the `measurability` tactic.

Note that `measurability` uses `fun_prop` for solving measurability of functions, so statements
about `Measurable`, `AEMeasurable`, `StronglyMeasurable` and `AEStronglyMeasurable` should be tagged
with `fun_prop` rather that `measurability`. The `measurability` attribute is equivalent to
`fun_prop` in these cases for backward compatibility with the earlier implementation.
-/
syntax (name := measurability) "measurability" : attr

initialize registerBuiltinAttribute {
  name := `measurability
  descr :=
    "The `measurability` attribute used to tag measurability statements for the `measurability` " ++
    "tactic."
  add decl stx kind := MetaM.run' do
    if ← isFunPropGoal (← getConstInfo decl).type then
      try
        Attribute.add decl `fun_prop (← `(attr|fun_prop)) kind
      catch e =>
        logWarningAt stx m!"This theorem will not be used by `measurability`: {e.toMessageData}"
    else
      Attribute.add decl `aesop
        (← `(attr|aesop safe apply (rule_sets := [$(mkIdent `Measurable):ident]))) kind
  erase decl := MetaM.run' do
    if ← isFunPropGoal (← getConstInfo decl).type then
      Attribute.erase decl `fun_prop
    else
      Attribute.erase decl `aesop
}

/--
The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute.

Note that `measurability` uses `fun_prop` for solving measurability of functions, so statements
about `Measurable`, `AEMeasurable`, `StronglyMeasurable` and `AEStronglyMeasurable` should be tagged
with `fun_prop` rather that `measurability`. The `measurability` attribute is equivalent to
`fun_prop` in these cases for backward compatibility with the earlier implementation.
-/
macro (name := Mathlib.Tactic.measurability) "measurability" : tactic =>
  `(tactic| aesop (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))

/--
The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success. -/
macro (name := Mathlib.Tactic.measurability?) "measurability?" : tactic =>
  `(tactic| aesop? (config := { terminal := true })
    (rule_sets := [$(Lean.mkIdent `Measurable):ident]))

-- Todo: implement `measurability!` and `measurability!?` and add configuration,
-- original syntax was (same for the missing `measurability` variants):
@[tactic_alt Mathlib.Tactic.measurability]
syntax (name := measurability!) "measurability!" : tactic
@[tactic_alt Mathlib.Tactic.measurability?]
syntax (name := measurability!?) "measurability!?" : tactic
