/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "multiGoal" linter

The "multiGoal" linter emits a warning where there is more than a single goal in scope.
There are a few tactics that are intended to work specifically in such a situation and the linter
ignores them.

Otherwise, whenever a tactic leaves multiple goals, the linter will emit a warning, unless
some form of "focusing" tactic is used.
Typically, the focusing is achieved by the `cdot`: `·`, but, e.g., `focus` or `on_goal x` also
serve a similar purpose.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "multiGoal" linter emits a warning when there are multiple active goals. -/
register_option linter.multiGoal : Bool := {
  defValue := true
  descr := "enable the multiGoal linter"
}

namespace multiGoal

/-- these are the `SyntaxNodeKind`s of tactics that we allow to have "inactive" goals.
Reasons for admitting a kind in `exclusions` include
* the tactic is reordering the goals, e.g. `swap`, `rotate_left`, ...;
* the tactic is structuring a proof, e.g. `skip`, `<;>`, ...;
* the tactic is creating new goals, e.g. `constructor`, `cases`, `induction`, ....
-/
abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert ``Lean.Parser.Term.cdot
  |>.insert ``cdot
  |>.insert ``cdotTk
  |>.insert ``Lean.Parser.Tactic.case
  |>.insert `«;»
  |>.insert `«<;>»
  |>.insert ``Lean.Parser.Tactic.«tactic_<;>_»
  |>.insert `«{»
  |>.insert `«]»
  |>.insert `null
  |>.insert `Std.Tactic.tacticSwap
  |>.insert ``Lean.Parser.Tactic.rotateLeft
  |>.insert ``Lean.Parser.Tactic.rotateRight
  |>.insert ``Lean.Parser.Tactic.skip
  |>.insert `Std.Tactic.«tacticOn_goal-_=>_»
  |>.insert `Mathlib.Tactic.«tacticSwap_var__,,»
  |>.insert ``Lean.Parser.Tactic.constructor
  |>.insert ``Lean.Parser.Tactic.tacticSeqBracketed
  |>.insert `Mathlib.Tactic.tacticAssumption'
  |>.insert ``Lean.Parser.Tactic.induction
  |>.insert ``Lean.Parser.Tactic.tacticTry_
  |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
  |>.insert ``Lean.Parser.Tactic.tacticSeq
  |>.insert ``Lean.Parser.Tactic.paren
  |>.insert ``Lean.Parser.Tactic.cases
  |>.insert ``Lean.Parser.Tactic.«tacticNext_=>_»
  |>.insert `then
  |>.insert `else
  |>.insert ``Lean.Parser.Tactic.intros
  |>.insert ``Lean.Parser.Tactic.tacticRepeat_
  |>.insert ``Lean.Parser.Tactic.injections
  |>.insert ``Lean.Parser.Tactic.substVars
  |>.insert `Std.Tactic.«tacticPick_goal-_»
  |>.insert ``Lean.Parser.Tactic.case'

/-- these are `SyntaxNodeKind`s that block the linter. -/
abbrev ignoreBranch : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert ``Lean.Parser.Tactic.Conv.conv
  |>.insert `Mathlib.Tactic.Conv.convLHS
  |>.insert `Mathlib.Tactic.Conv.convRHS
  |>.insert ``Lean.Parser.Tactic.first
  |>.insert ``Lean.Parser.Tactic.repeat'
  |>.insert ``Lean.Parser.Tactic.tacticIterate____
  |>.insert ``Lean.Parser.Tactic.anyGoals
  |>.insert ``Lean.Parser.Tactic.allGoals
  |>.insert ``Lean.Parser.Tactic.focus

/-- `getManyGoals` returns the syntax nodes where the tactic leaves at least one goal that
was not present before it ran,
unless its `SyntaxNodeKind` is either in `exclusions` or in `ignoreBranch`.
-/
partial
def getManyGoals : InfoTree → Array (Syntax × Nat)
  | .node k args =>
    let kargs := (args.map getManyGoals).foldl (· ++ ·) #[]
    if let .ofTacticInfo i := k then
      if ignoreBranch.contains i.stx.getKind then #[] else
      if let  .original .. := i.stx.getHeadInfo then
        let newGoals := i.goalsAfter.filter (i.goalsBefore.contains ·)
        if newGoals.length != 0 && !exclusions.contains i.stx.getKind then
          kargs.push (i.stx, newGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => default

end multiGoal

end Mathlib.Linter

namespace Mathlib.Linter.multiGoal

/-- Gets the value of the `linter.multiGoal` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.multiGoal o

@[inherit_doc Mathlib.Linter.linter.multiGoal]
def multiGoalLinter : Linter where
  run := withSetOptionIn fun _stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, n) in getManyGoals t do
        let gl := if n == 1 then "goal" else "goals"
        Linter.logLint linter.multiGoal s (m!"'{s}' leaves {n} {gl} '{s.getKind}'")

initialize addLinter multiGoalLinter
