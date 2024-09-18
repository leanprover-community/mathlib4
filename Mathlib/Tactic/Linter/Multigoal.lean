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
ignores them. Otherwise, whenever a tactic leaves multiple goals, the linter will emit a warning,
unless some form of "focusing" tactic is used.
Typically, the focusing is achieved by the `cdot`: `·`, but, e.g., `focus` or `on_goal x` also
serve a similar purpose.

TODO:
* Should the linter flag unnecessary scoping as well?
  For instance, should
  ```lean
  example : True := by
    · · exact .intro
  ```
  raise a warning?
* Custom support for "accumulating side-goals", so that once they are all in scope
  they can be solved in bulk via `all_goals` or a similar tactic.
* In development, `on_goal` has been partly used as a way of silencing the linter
  precisely to allow the accumulation referred to in the previous item.
  Maybe revisit usages of `on_goal` and also nested `induction` and `cases`.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "multiGoal" linter emits a warning when there are multiple active goals. -/
register_option linter.style.multiGoal : Bool := {
  defValue := true
  descr := "enable the multiGoal linter"
}

namespace Style.multiGoal

/-- These are the `SyntaxNodeKind`s of tactics that we allow to have "inactive" goals.
Reasons for admitting a kind in `exclusions` include
* the tactic is reordering the goals, e.g. `swap`, `rotate_left`, ...;
* the tactic is structuring a proof, e.g. `skip`, `<;>`, ...;
* the tactic is creating new goals, e.g. `constructor`, `cases`, `induction`, ....
Tactic combinators like `repeat` or `try` are a mix of both.
-/
abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  -- structuring a proof
  |>.insert ``Lean.Parser.Term.cdot
  |>.insert ``cdot
  |>.insert ``cdotTk
  |>.insert ``Lean.Parser.Tactic.tacticSeqBracketed
  |>.insert `«;»
  |>.insert `«<;>»
  |>.insert ``Lean.Parser.Tactic.«tactic_<;>_»
  |>.insert `«{»
  |>.insert `«]»
  |>.insert `null
  |>.insert `then
  |>.insert `else
  |>.insert ``Lean.Parser.Tactic.«tacticNext_=>_»
  |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
  |>.insert ``Lean.Parser.Tactic.tacticSeq
  -- re-ordering goals
  |>.insert `Batteries.Tactic.tacticSwap
  |>.insert ``Lean.Parser.Tactic.rotateLeft
  |>.insert ``Lean.Parser.Tactic.rotateRight
  |>.insert ``Lean.Parser.Tactic.skip
  |>.insert `Batteries.Tactic.«tacticOn_goal-_=>_»
  |>.insert `Mathlib.Tactic.«tacticSwap_var__,,»
  -- tactic combinators
  |>.insert ``Lean.Parser.Tactic.tacticRepeat_
  |>.insert ``Lean.Parser.Tactic.tacticTry_
  -- creating new goals
  |>.insert ``Lean.Parser.Tactic.paren
  |>.insert ``Lean.Parser.Tactic.case
  |>.insert ``Lean.Parser.Tactic.constructor
  |>.insert `Mathlib.Tactic.tacticAssumption'
  |>.insert ``Lean.Parser.Tactic.induction
  |>.insert ``Lean.Parser.Tactic.cases
  |>.insert ``Lean.Parser.Tactic.intros
  |>.insert ``Lean.Parser.Tactic.injections
  |>.insert ``Lean.Parser.Tactic.substVars
  |>.insert `Batteries.Tactic.«tacticPick_goal-_»
  |>.insert ``Lean.Parser.Tactic.case'
  |>.insert `«tactic#adaptation_note_»

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
  | .node info args =>
    let kargs := (args.map getManyGoals).foldl (· ++ ·) #[]
    if let .ofTacticInfo info := info then
      if ignoreBranch.contains info.stx.getKind then #[] else
      if let .original .. := info.stx.getHeadInfo then
        let newGoals := info.goalsAfter.filter (info.goalsBefore.contains ·)
        if newGoals.length != 0 && !exclusions.contains info.stx.getKind then
          kargs.push (info.stx, newGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => default

/-- The linter only considers files whose name begins with a component in `libraries`. -/
abbrev libraries : HashSet Name := HashSet.empty
  |>.insert `Mathlib
  |>.insert `Archive
  |>.insert `Counterexamples

/-- Gets the value of the `linter.style.multiGoal` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.style.multiGoal o

@[inherit_doc Mathlib.Linter.linter.style.multiGoal]
def multiGoalLinter : Linter where
  run := withSetOptionIn fun _stx => do
    let mod ← getMainModule
    unless getLinterHash (← getOptions) &&
        -- the linter only runs on `Mathlib`, `Archive`, `Counterexamples` and its own test file
        (libraries.contains (mod.components.getD 0 default) || mod == `test.Multigoal) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, n) in getManyGoals t do
        let gl := if n == 1 then "goal" else "goals"
        Linter.logLint linter.style.multiGoal s (m!"'{s}' leaves {n} {gl} '{s.getKind}'")

initialize addLinter multiGoalLinter

end Style.multiGoal

end Mathlib.Linter
