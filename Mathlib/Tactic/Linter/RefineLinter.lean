/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "refine" linter

The "refine" linter flags usages of `refine'`.

The tactics `refine` and `refine'` are similar, but they handle meta-variable slightly differently.
This means that they are not completely interchangeable, nor can one completely replace the other.
However, `refine` is more readable and (heuristically) tends to be more efficient on average.

This linter is an incentive to discourage uses of `refine'`, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter.refine

/-- The refine linter emits a warning on usages of `refine'`. -/
register_option linter.refine : Bool := {
  defValue := true
  descr := "enable the refine linter"
}

/-- `getRefine' t` returns all usages of `refine'` in the input syntax. -/
partial
def getRefine' : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let rargs := (args.map getRefine').flatten
    if kind == ``Lean.Parser.Tactic.refine' then rargs.push stx else rargs
  | _ => default

/-- Gets the value of the `linter.refine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine o

/-- The main implementation of the refine linter. -/
def refineLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stx in (getRefine' _stx) do
    Linter.logLint linter.refine stx "Please, use `refine` or `apply` instead of `refine'`!"

initialize addLinter refineLinter
