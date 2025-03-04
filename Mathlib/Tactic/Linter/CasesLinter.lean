/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Damiano Testa
-/
import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header

/-!
# The "cases" linter

The "cases" linter flags uses of the `cases'` tactic, which is a backward-compatible version of
Lean 3's `cases` tactic. Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by
`cases'` are not required to be separated by case, which hinders readability.

This linter is an incentive to discourage uses of `cases'`, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter.Style

/-- The "cases" linter flags uses of the `cases'` tactic, which is a backward-compatible version of
Lean 3's `cases` tactic. Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by
`cases'` are not required to be separated by case, which hinders readability.
-/
register_option linter.style.cases : Bool := {
  defValue := false
  descr := "enable the cases linter"
}

/-- `getCases' t` returns all usages of the `cases'` tactic in the input syntax `t`. -/
partial
def getCases' : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let rargs := (args.map getCases').flatten
    if kind == `Mathlib.Tactic.cases' then rargs.push stx else rargs
  | _ => default

@[inherit_doc linter.style.cases]
def casesLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.style.cases (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stx in (getCases' _stx) do
    Linter.logLint linter.style.cases stx
      "The `cases'` tactic is discouraged: \
      please strongly consider using `obtain`, `rcases` or `cases` instead."

initialize addLinter casesLinter

end Mathlib.Linter.Style
