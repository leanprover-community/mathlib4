/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
#  The "multiGoal" linter

The "multiGoal" linter emits a warning where there is more than a single goal in scope.
There is an exception: a tactic that closes *all* remaining goals is allowed.

There are a few tactics, such as `skip`, `swap` or the `try` combinator, that are intended to work
specifically in such a situation.
Otherwise, the mathlib style guide ask that goals be be focused until there is only one active goal
at a time.
If this focusing does not happen, the linter emits a warning.
Typically, the focusing is achieved by the `cdot`: `·`, but, e.g., `focus` or `on_goal x`
also serve a similar purpose.

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

/-- The `SyntaxNodeKind`s in `exclusions` correspond to tactics that the linter allows,
even though there are multiple active goals.
Reasons for admitting a kind in `exclusions` include
* the tactic focuses on one goal, e.g. `·`, `focus`, `on_goal i =>`, ...;
* the tactic is reordering the goals, e.g. `swap`, `rotate_left`, ...;
* the tactic is structuring a proof, e.g. `skip`, `<;>`, ...;
* the tactic is creating new goals, e.g. `constructor`, `cases`, `induction`, ....

There is some overlap in scope between `ignoreBranch` and `exclusions`.

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
    `«tactic#adaptation_note_»,
    `tacticSleep_heartbeats_
  ]

/-- The `SyntaxNodeKind`s in `ignoreBranch` correspond to tactics that disable the linter from
their first application until the corresponding proof branch is closed.
Reasons for ignoring these tactics include
* the linter gets confused by the proof management, e.g. `conv`;
* the tactics are *intended* to act on multiple goals, e.g. `repeat`, `any_goals`, `all_goals`, ...

There is some overlap in scope between `exclusions` and `ignoreBranch`.
-/
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

/--
`getNonTerminalCdots stx` extracts the position of the syntax nodes contained in `stx`
whose `SyntaxNodeKind` is `cdot` and that are not preceded by a `cdot`s.
These are candidates for unnecessary uses of `cdot`:
if there is only one active goal before placing `·`, then they will be flagged.
-/
partial
def getNonTerminalCdots : Syntax → Array String.Pos
  | .node _ _ args =>
    Id.run do
    let mut nonCDotFollowers := #[]
    let mut wasCDot? := false
    for i in [:args.size] do
      if i % 2 == 1 then continue
      let argi := args[i]!
      if (! wasCDot?) && argi.isOfKind ``cdot then
        nonCDotFollowers := nonCDotFollowers.push (argi.getPos?.getD default)
      wasCDot? := argi.isOfKind `cdot
    return nonCDotFollowers ++ (args.map getNonTerminalCdots).flatten
  | _ => default

variable (unCDots : Array String.Pos) in
/-- `getManyGoals t` returns the syntax nodes of the `InfoTree` `t` corresponding to tactic calls
which
* leave at least one goal that was not present before it ran;
* are not excluded through `exclusions` or `ignoreBranch`.

The `Option Nat` value is `none` if the linter should flag the node as an unnecessary `·`.
Otherwise, it is `some n`, where `n` is the number of active goals after applying the
tactic that were not also goals before applying the tactic.
-/
partial
def getManyGoals : InfoTree → Array (Syntax × Option Nat)
  | .node info args =>
    let kargs := (args.map getManyGoals).toArray.flatten
    if let .ofTacticInfo info := info then
      if ignoreBranch.contains info.stx.getKind then #[] else
      if let .original .. := info.stx.getHeadInfo then
        let newGoals := info.goalsAfter.filter (info.goalsBefore.contains ·)
        -- record unnecessary uses of `·`
        if unCDots.contains (info.stx.getPos?.getD default) && info.goalsBefore.length == 1 then
        --if info.stx.isOfKind `Lean.cdot &&
        --    unCDots.contains (info.stx.getPos?.getD default) &&
        --    info.goalsBefore.length == 1 &&
        --    info.goalsAfter.length != 0 then
          kargs.push (info.stx, none) else
        if newGoals.length != 0 && !exclusions.contains info.stx.getKind then
          kargs.push (info.stx, newGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => default

@[inherit_doc Mathlib.Linter.linter.style.multiGoal]
def multiGoalLinter : Linter where run := withSetOptionIn fun _stx ↦ do
    let poss := getNonTerminalCdots _stx
    unless Linter.getLinterValue linter.style.multiGoal (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let trees ← getInfoTrees
    for t in trees.toArray do
      for (s, n) in getManyGoals poss t do
        match n with
          | none =>
            Linter.logLint linter.style.multiGoal s
              m!"Unnecessary focusing dot `·`: you should be able to remove it, \
                or move it earlier up in the proof, as necessary.\n\
                '{s.getKind}'"
          | some n =>
            Linter.logLint linter.style.multiGoal s
              m!"There are {n+1} unclosed goals before '{s}' and \
                at least one remaining goal afterwards.\n\
                Please focus on the current goal, for instance using `·` (typed as \"\\.\")."

initialize addLinter multiGoalLinter

end Style.multiGoal

end Mathlib.Linter
