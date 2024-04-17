/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "terminal refine" linter

The "terminal refine" linter flags terminal usages of `refine`.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The terminal refine linter emits a warning on terminal usages of `refine`. -/
register_option linter.terminalRefine : Bool := {
  defValue := true
  descr := "enable the terminal refine linter"
}

namespace terminalRefine

/-- `refine? stx` detects whether the input syntax `stx` is `refine` or `refine'`. -/
def refine? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.refine' _ => true
  | .node _ ``Lean.Parser.Tactic.refine _  => true
  | _ => false

/-- `SyntaxNodeKinds` that "contain" a `refine` and that the linter should ignore. -/
abbrev ignore : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert `Mathlib.Tactic.useSyntax
  |>.insert `Mathlib.Tactic.«tacticUse!___,,»
  |>.insert `Mathlib.Tactic.congrM

/-- `refine_tree t` returns all terminal usages of `refine/refine'` in the input infotree. -/
partial
def refine_tree : InfoTree → Array Syntax
  | .node k args =>
    let rargs := (args.map refine_tree).toArray.flatten
    if let .ofTacticInfo i := k then
      let stx := i.stx
      if ! ignore.contains stx.getKind then
        if (refine? stx) &&
          (i.goalsAfter.length + 1 == i.goalsBefore.length &&  -- would `<` be enough?
            (i.goalsAfter.map i.goalsBefore.contains).all (·)) then rargs.push stx
        else rargs
      else #[]
    else rargs
  | .context _ t => refine_tree t
  | _ => default

end terminalRefine

end Mathlib.Linter

namespace Mathlib.Linter.terminalRefine

/-- Gets the value of the `linter.terminalRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.terminalRefine o

/-- The main implementation of the terminal refine linter. -/
def terminalRefineLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  for t in trees.toArray do
    for stx in (refine_tree t) do
      Linter.logLint linter.terminalRefine stx
        m!"Please, use `exact` instead of `{stx.getKind.components.getLastD `refine}`!"

initialize addLinter terminalRefineLinter
