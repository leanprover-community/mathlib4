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
  defValue := false
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
abbrev exclusions : Std.HashSet SyntaxNodeKind := .ofList [
    -- structuring a proof
    ``Lean.Parser.Term.cdot,
    ``cdot,
    ``cdotTk,
    ``Lean.Parser.Tactic.tacticSeqBracketed,
    `«;»,
    `«<;>»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    `«{»,
    `«]»,
    `null,
    `then,
    `else,
    ``Lean.Parser.Tactic.«tacticNext_=>_»,
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    -- re-ordering goals
    `Batteries.Tactic.tacticSwap,
    ``Lean.Parser.Tactic.rotateLeft,
    ``Lean.Parser.Tactic.rotateRight,
    ``Lean.Parser.Tactic.skip,
    `Batteries.Tactic.«tacticOn_goal-_=>_»,
    `Mathlib.Tactic.«tacticSwap_var__,,»,
    -- tactic combinators
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticTry_,
    -- creating new goals
    ``Lean.Parser.Tactic.paren,
    ``Lean.Parser.Tactic.case,
    ``Lean.Parser.Tactic.constructor,
    `Mathlib.Tactic.tacticAssumption',
    ``Lean.Parser.Tactic.induction,
    ``Lean.Parser.Tactic.cases,
    ``Lean.Parser.Tactic.intros,
    ``Lean.Parser.Tactic.injections,
    ``Lean.Parser.Tactic.substVars,
    `Batteries.Tactic.«tacticPick_goal-_»,
    ``Lean.Parser.Tactic.case',
    `«tactic#adaptation_note_»
  ]

/-- these are `SyntaxNodeKind`s that block the linter. -/
abbrev ignoreBranch : Std.HashSet SyntaxNodeKind := .ofList [
    ``Lean.Parser.Tactic.Conv.conv,
    `Mathlib.Tactic.Conv.convLHS,
    `Mathlib.Tactic.Conv.convRHS,
    ``Lean.Parser.Tactic.first,
    ``Lean.Parser.Tactic.repeat',
    ``Lean.Parser.Tactic.tacticIterate____,
    ``Lean.Parser.Tactic.anyGoals,
    ``Lean.Parser.Tactic.allGoals,
    ``Lean.Parser.Tactic.focus
  ]

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

@[inherit_doc Mathlib.Linter.linter.style.multiGoal]
def multiGoalLinter : Linter where
  run := withSetOptionIn fun _stx => do
    unless Linter.getLinterValue linter.style.multiGoal (← getOptions) do
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
