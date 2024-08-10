/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Adomas Baliuka
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
# The "admit" linter

The "admit" linter flags usages of the `admit` tactic.

The tactics `admit` and `sorry` are synonyms.
The use of `sorry` is much more common and should be preferred.

This linter is an incentive to discourage uses of `admit`, without being a ban.
-/

open Lean Elab

namespace Mathlib.Linter.admit

/-- The admit linter emits a warning on usages of `admit`. -/
register_option linter.admit : Bool := {
  defValue := true
  descr := "enable the admit linter"
}

syntax (name := admit) "admit " : tactic
/-- `admit` is a shorthand for `exact sorry`. -/
macro "admit" : tactic => `(tactic| exact @sorryAx _ false)

/-- `getadmit t` returns all usages of the `admit` tactic in the input syntax `t`. -/
partial
def getadmit : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let rargs := (args.map getadmit).flatten
    if kind == ``admit then rargs.push stx else rargs
  | _ => default

/-- The "admit" linter flags usages of the `admit` tactic.

The tactics `admit` and `sorry` are synonyms.
The use of `sorry` is much more common and should be preferred.
-/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.admit o

@[inherit_doc getLinterHash]
def admitLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for stx in (getadmit _stx) do
    Linter.logLint linter.admit stx
      "The `admit` tactic is discouraged: \
      please consider using the synonymous `sorry` instead."

initialize addLinter admitLinter

end Mathlib.Linter.admit
