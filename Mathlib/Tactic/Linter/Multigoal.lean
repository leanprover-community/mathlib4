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
#  The "multiGoal" linter

The "multiGoal" linter emits a warning where there is more than a single goal in scope.
There is an exception: a tactic that closes *all* remaining goals is allowed.

There are a few tactics, such as `skip`, `swap` or the `try` combinator, that are intended to work
specifically in such a situation.
Otherwise, the mathlib style guide ask that goals be focused until there is only one active goal
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

open Lean Elab Linter

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
abbrev exclusions : Std.HashSet SyntaxNodeKind := .ofArray #[
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
    ``Lean.Parser.Tactic.focus,
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
abbrev ignoreBranch : Std.HashSet SyntaxNodeKind := .ofArray #[
    ``Lean.Parser.Tactic.Conv.conv,
    `Mathlib.Tactic.Conv.convLHS,
    `Mathlib.Tactic.Conv.convRHS,
    ``Lean.Parser.Tactic.first,
    ``Lean.Parser.Tactic.repeat',
    ``Lean.Parser.Tactic.tacticIterate____,
    ``Lean.Parser.Tactic.anyGoals,
    ``Lean.Parser.Tactic.allGoals,
    ``Lean.Parser.Tactic.failIfSuccess,
    `Mathlib.Tactic.successIfFailWithMsg
  ]

/-- `getManyGoals t` returns the syntax nodes of the `InfoTree` `t` corresponding to tactic calls
which
* leave at least one goal that was present before it ran
  (with the exception of tactics that leave the sole goal unchanged);
* are not excluded through `exclusions` or `ignoreBranch`;

together with the number of goals before the tactic,
the number of goals after the tactic, and the number of unaffected goals.
-/
partial
def getManyGoals : InfoTree → Array (Syntax × Nat × Nat × Nat)
  | .node info args =>
    let kargs := (args.map getManyGoals).toArray.flatten
    if let .ofTacticInfo info := info then
      if ignoreBranch.contains info.stx.getKind then #[]
      -- Ideal case: one goal, and it might or might not be closed.
      else if info.goalsBefore.length == 1 && info.goalsAfter.length ≤ 1 then kargs
      else if let .original .. := info.stx.getHeadInfo then
        let backgroundGoals := info.goalsAfter.filter (info.goalsBefore.contains ·)
        if backgroundGoals.length != 0 && !exclusions.contains info.stx.getKind then
          kargs.push (info.stx,
                      info.goalsBefore.length, info.goalsAfter.length, backgroundGoals.length)
        else kargs
      else kargs
    else kargs
  | .context _ t => getManyGoals t
  | _ => default

@[inherit_doc Mathlib.Linter.linter.style.multiGoal]
def multiGoalLinter : Linter where run := withSetOptionIn fun _stx ↦ do
    unless getLinterValue linter.style.multiGoal (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let trees ← getInfoTrees
    for t in trees do
      for (s, before, after, n) in getManyGoals t do
        let goals (k : Nat) := if k == 1 then f!"1 goal" else f!"{k} goals"
        let fmt ← Command.liftCoreM
          try PrettyPrinter.ppTactic ⟨s⟩ catch _ => pure f!"(failed to pretty print)"
        Linter.logLint linter.style.multiGoal s m!"\
          The following tactic starts with {goals before} and ends with {goals after}, \
          {n} of which {if n == 1 then "is" else "are"} not operated on.\
          {indentD fmt}\n\
          Please focus on the current goal, for instance using `·` (typed as \"\\.\")."

initialize addLinter multiGoalLinter

end Style.multiGoal

end Mathlib.Linter
