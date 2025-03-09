/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# The "refine" linter

The "refine" linter flags usages of the `refine'` tactic.

The tactics `refine` and `refine'` are similar, but they handle meta-variables slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.

This linter is an incentive to discourage uses of `refine'`, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "refine" linter flags usages of the `refine'` tactic.

The tactics `refine` and `refine'` are similar, but they handle meta-variables slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.
-/
register_option linter.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}

/-- `getRefine' t` returns all usages of the `refine'` tactic in the input syntax `t`. -/
partial
def getRefineCases' : Syntax → Array Syntax × Array Syntax
  | stx@(.node _ kind args) =>
    let (refine's, cases's) := (args.map getRefineCases').foldl (init := (#[], #[])) fun
      (totRefine, totCases) (rs, cs) => (totRefine ++ rs, totCases ++ cs)
    if ``Lean.Parser.Tactic.refine' == kind then (refine's.push stx, cases's)
    else if `Mathlib.Tactic.cases' == kind then (refine's, cases's.push stx)
    else (refine's, cases's)
  | _ => default

@[inherit_doc linter.refine]
def refineLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.refine (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let (refine's, cases') := getRefineCases' stx
  for stx' in refine's do
    Linter.logLint linter.refine stx'
      "The `refine'` tactic is discouraged: \
      please strongly consider using `refine` or `apply` instead."
  for stx' in cases' do
    Linter.logLint linter.refine stx'
      "The `cases'` tactic is discouraged: \
      please strongly consider using `obtain`, `rcases` or `cases` instead."

initialize addLinter refineLinter

end Mathlib.Linter
