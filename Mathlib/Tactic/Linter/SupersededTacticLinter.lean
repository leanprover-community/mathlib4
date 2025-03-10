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
# Linter against superseded tactics (refine' and cases')

`refine'` and `cases'` provide backward-compatible implementations of their unprimed equivalents
in Lean 3, `refine` and `cases`. This linter flags usages of these two tactics, because they have
been superseded by Lean 4 tactics:

* `refine` replaces `refine'`. While they are similar, they handle metavariables slightly
  differently; this means that they are not completely interchangeable, nor can one completely
  replace the other. However, `refine` is more readable and (heuristically) tends to be more
  efficient on average.
* `obtain`, `rcases` and `cases` replace `cases'`. Unlike the replacement tactics, `cases'`
  does not require the variables it introduces to be separated by case, which hinders readability.

This linter is an incentive to discourage uses of such superseded tactics, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter.Style

/-- The "refine" linter flags usages of the `refine'` tactic.

The tactics `refine` and `refine'` are similar, but they handle meta-variables slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.
-/
register_option linter.style.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}

/-- The "cases" linter flags uses of the `cases'` tactic, which is a backward-compatible version of
Lean 3's `cases` tactic. Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by
`cases'` are not required to be separated by case, which hinders readability.
-/
register_option linter.style.cases : Bool := {
  defValue := false
  descr := "enable the cases linter"
}

/-- `getSupersededTactics t` returns all usages of superseded tactics in the input syntax `t`. -/
partial
def getSupersededTactics : Syntax → Array (Nat × Syntax × MessageData)
  | stx@(.node _ kind args) =>
    let rargs := (args.map getSupersededTactics).flatten
    if ``Lean.Parser.Tactic.refine' == kind then
      rargs.push (0, stx, "The `refine'` tactic is discouraged: \
                           please strongly consider using `refine` or `apply` instead.")
    else if `Mathlib.Tactic.cases' == kind then
      rargs.push (1, stx, "The `cases'` tactic is discouraged: \
                           please strongly consider using `obtain`, `rcases` or `cases` instead.")
    else rargs
  | _ => default

/-- The superseded tactics linter flags usages of superseded tactics and suggests
replacement tactics.

Currently `refine'` (superseded by `refine`) and `cases'` (superseded by `obtain`, `rcases` and
`cases`) are flagged. The linter can be turned off for these cases individually with the options
`linter.style.refine` and `linter.style.cases`.
-/
def supersededTacticsLinter : Linter where run := withSetOptionIn fun stx => do
  if (← MonadState.get).messages.hasErrors then
    return
  for (kind, stx', msg) in getSupersededTactics stx do
    match kind with
    | 0 => Linter.logLintIf linter.style.refine stx' msg
    | 1 => Linter.logLintIf linter.style.cases stx' msg
    | _ => continue

initialize addLinter supersededTacticsLinter

end Mathlib.Linter.Style
