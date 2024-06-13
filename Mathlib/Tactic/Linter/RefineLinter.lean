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
-/

open Lean Elab

namespace Mathlib.Linter.refine

/-- The refine linter emits a warning on usages of `refine'`. -/
register_option linter.refine : Bool := {
  defValue := true
  descr := "enable the refine linter"
}

/-- `refine_tree t` returns all usages of `refine'` is the input infotree. -/
partial
def refine_tree : InfoTree → Array Syntax
  | .node k args =>
    let rargs := (args.map refine_tree).toArray.flatten
    if let .ofTacticInfo i := k then
      if i.stx.isOfKind ``Lean.Parser.Tactic.refine' then rargs.push i.stx else rargs
    else rargs
  | .context _ t => refine_tree t
  | _ => default

/-- Gets the value of the `linter.refine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine o

/-- The main implementation of the refine linter. -/
def refineLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  for t in trees.toArray do
    for stx in (refine_tree t) do
      Linter.logLint linter.refine stx "Please, use `refine` instead of `refine'`!"

initialize addLinter refineLinter
