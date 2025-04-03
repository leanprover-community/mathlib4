/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jeremy Tan
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# Linter against deprecated syntax

`refine'` and `cases'` provide backward-compatible implementations of their unprimed equivalents
in Lean 3, `refine` and `cases`. They have been superseded by Lean 4 tactics:

* `refine` replaces `refine'`. While they are similar, they handle metavariables slightly
  differently; this means that they are not completely interchangeable, nor can one completely
  replace the other. However, `refine` is more readable and (heuristically) tends to be more
  efficient on average.
* `obtain`, `rcases` and `cases` replace `cases'`. Unlike the replacement tactics, `cases'`
  does not require the variables it introduces to be separated by case, which hinders readability.

This linter is an incentive to discourage uses of such deprecated syntax, without being a ban.
It is not inherently limited to tactics.
-/

open Lean Elab

namespace Mathlib.Linter.Style

/-- The option `linter.style.refine` of the deprecated syntax linter flags usages of
the `refine'` tactic.

The tactics `refine` and `refine'` are similar, but they handle meta-variables slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.
-/
register_option linter.style.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}

/-- The option `linter.style.cases` of the deprecated syntax linter flags usages of
the `cases'` tactic, which is a backward-compatible version of Lean 3's `cases` tactic.
Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by `cases'` are not
required to be separated by case, which hinders readability.
-/
register_option linter.style.cases : Bool := {
  defValue := false
  descr := "enable the cases linter"
}

/-- `getDeprecatedSyntax t` returns all usages of deprecated syntax in the input syntax `t`. -/
partial
def getDeprecatedSyntax : Syntax → Array (SyntaxNodeKind × Syntax × MessageData)
  | stx@(.node _ kind args) =>
    let rargs := (args.map getDeprecatedSyntax).flatten
    if ``Lean.Parser.Tactic.refine' == kind then
      rargs.push (kind, stx,
        "The `refine'` tactic is discouraged: \
         please strongly consider using `refine` or `apply` instead.")
    else if `Mathlib.Tactic.cases' == kind then
      rargs.push (kind, stx,
        "The `cases'` tactic is discouraged: \
         please strongly consider using `obtain`, `rcases` or `cases` instead.")
    else rargs
  | _ => default

/-- The deprecated syntax linter flags usages of deprecated syntax and suggests
replacement syntax.

Currently `refine'` (superseded by `refine`) and `cases'` (superseded by `obtain`, `rcases` and
`cases`) are flagged. The linter can be turned off for these cases individually with the options
`linter.style.refine` and `linter.style.cases`.
-/
def deprecatedSyntaxLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.refine (← getOptions) ||
      Linter.getLinterValue linter.style.cases (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (kind, stx', msg) in getDeprecatedSyntax stx do
    match kind with
    | ``Lean.Parser.Tactic.refine' => Linter.logLintIf linter.style.refine stx' msg
    | `Mathlib.Tactic.cases' => Linter.logLintIf linter.style.cases stx' msg
    | _ => continue

initialize addLinter deprecatedSyntaxLinter

end Mathlib.Linter.Style
