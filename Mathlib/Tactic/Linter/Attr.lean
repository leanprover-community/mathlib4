/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Lean.Linter.Basic

/-! # The Mathlib standard linters

This file defines which set of linters should be enabled by default in Mathlib and other projects
that aim for the same quality standards.
-/

open Lean Linter

/-- `linter.mathlibStandard` enables all the linters defined and used in Mathlib. -/
register_option linter.mathlibStandard : Bool := {
  defValue := false
  descr := "enable the Mathlib linters"
}

/-- The list of linter settings enabled in Mathlib. -/
abbrev mathlibStandardLinters : NameMap DataValue := .ofList [
  -- The `docPrime` linter is disabled: https://github.com/leanprover-community/mathlib4/issues/20560
  ⟨`linter.docPrime, false⟩,
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.oldObtain, true⟩,
  ⟨`linter.style.cases, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.docString, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  ⟨`linter.style.header, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.style.longLine, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.multiGoal, true⟩,
  ⟨`linter.style.openClassical, true⟩,
  ⟨`linter.style.refine, true⟩,
  ⟨`linter.style.setOption, true⟩
]

/-- Are Mathlib-standard linters enabled? -/
def Mathlib.standardLintersEnabled (o : Options) : Bool :=
  o.get linter.mathlibStandard.name false

/-- Return whether a linter should be enabled.

If the value of `opt` has been set using the `set_option` command, return that setting.
Otherwise this function returns true if:
* the linter is enabled by default, or
* all linters are enabled (by `set_option linter.all true`), or
* Mathlib-standard linters are enabled and `opt` is a Mathlib-standard linter.
-/
def Mathlib.getLinterValue (opt : Lean.Option Bool) (o : Options) : Bool :=
  -- Always return the value that the option is explicitly set to, if any.
  if let some val := opt.get? o then
    val
  else
    -- Otherwise it could be a standard linter...
    (Mathlib.standardLintersEnabled o &&
      mathlibStandardLinters.find? opt.name == some (.ofBool true)) ||
    -- ... or it is enabled in the regular way.
    Lean.Linter.getLinterValue opt o

/-- Return a numeric value for this linter, or `0` if it is unset.

This function returns nonzero values in two cases:
* the option `opt` is set to a nonzero value, or
* Mathlib-standard linters are enabled and Mathlib sets `opt` to a nonzero value.
-/
def Mathlib.getLinterNat (opt : Lean.Option Nat) (o : Options) : Nat :=
  let setValue := opt.get o
  if setValue == 0 && Mathlib.standardLintersEnabled o then
    match mathlibStandardLinters.find? opt.name with
    | some (.ofNat n) => n
    | _ => 0
  else
    setValue
