/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.TryThis
import Std.Linter.UnreachableTactic
import Mathlib.Data.Nondet.Basic
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Mathport.Rename
import Mathlib.Data.MLList.Meta

/-!
# The `hint` tactic.

The `hint` tactic tries the kitchen sink:
it runs every tactic registered via the `register_hint tac` command
on the current goal, and reports which ones succeed.

-/

open Lean Elab Tactic

open Std.Tactic.TryThis

namespace Mathlib.Tactic.Hint

/-- An environment extension for registering hint tactics. -/
initialize hintExtension : SimplePersistentEnvExtension (TSyntax `tactic) (List (TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new hint tactic. -/
def addHint (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hintExtension.addEntry env stx

/-- Return the list of registered hint tactics. -/
def getHints : CoreM (List (TSyntax `tactic)) := return hintExtension.getState (← getEnv)

open Lean.Elab.Command in
/--
Register a tactic for use with the `hint` tactic, e.g. `register_hint simp_all`.
-/
elab (name := registerHintStx) "register_hint" tac:tactic : command => liftTermElabM do
  -- remove comments
  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
  addHint tac

initialize
  Std.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``registerHintStx

/--
Construct a suggestion for a tactic.
* Check the passed `MessageLog` for an info message beginning with "Try this: ".
* If found, use that as the suggestion.
* Otherwise use the provided syntax.
* Also, look for remaining goals and pretty print them after the suggestion.
-/
def suggestion (tac : TSyntax `tactic) (msgs : MessageLog := {}) : TacticM Suggestion := do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure (some str)
  let style? := if goals.isEmpty then some .success else none
  let msg? ← msgs.toList.findM? fun m => do pure <|
    m.severity == MessageSeverity.information && (← m.data.toString).startsWith "Try this: "
  let suggestion ← match msg? with
  | some m => pure <| SuggestionText.string (((← m.data.toString).drop 10).takeWhile (· != '\n'))
  | none => pure <| SuggestionText.tsyntax tac
  return { suggestion, postInfo?, style? }

/-- Run a tactic, returning any new messages rather than adding them to the message log. -/
def withMessageLog (t : TacticM Unit) : TacticM MessageLog := do
  let initMsgs ← modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
  t
  modifyGetThe Core.State fun st => (st.messages, { st with messages := initMsgs })

/--
Run a tactic, but revert any changes to info trees.
We use this to inhibit the creation of widgets by subsidiary tactics.
-/
def withoutInfoTrees (t : TacticM Unit) : TacticM Unit := do
  let trees := (← getInfoState).trees
  t
  modifyInfoState fun s => { s with trees }

/--
Run all tactics registered using `register_hint`,
returning a list of triples consisting of
* a `Suggestion` (for "Try this"),
* the `List MVarId` of remaining goals, and
* the `Tactic.SavedState` after running the tactic.

If one tactic succeeds and closes the goal, we cancel subsequent tactics.
-/
def hintCore : TacticM (Array (Suggestion × List MVarId × SavedState)) := do
  let tacs := (← getHints)
  let tasks := tacs.map fun t : TSyntax `tactic => do
    if let some msgs ← observing? (withMessageLog (withoutInfoTrees (evalTactic t))) then
      return some (← suggestion t msgs, ← getGoals, ← saveState)
    else
      return none
  let (cancel, results) ← TacticM.runGreedily tasks
  let results := results.filterMap id
  let results ← (results.takeUpToFirst fun r => r.2.1.isEmpty).asArray
  cancel -- Cancel any remaining tasks, in case one closed the goal early.
  return results.qsort (·.2.1.length < ·.2.1.length)

/--
Run all tactics registered using `register_hint`.
Print a "Try these:" suggestion for each of the successful tactics.

If one tactic succeeds and closes the goal, we cancel subsequent tactics.
-/
def hint (stx : Syntax) : TacticM Unit := do
  let results ← hintCore
  addSuggestions stx (results.map (·.1))
  match results.find? (·.2.1.isEmpty) with
  | some r =>
    -- We don't restore the entire state, as that would delete the suggestion messages.
    setMCtx r.2.2.term.meta.meta.mctx
  | none => admitGoal (← getMainGoal)

/--
The `hint` tactic tries every tactic registered using `register_hint tac`,
and reports any that succeed.
-/
syntax (name := hintStx) "hint" : tactic

@[inherit_doc hintStx]
elab_rules : tactic
  | `(tactic| hint%$tk) => hint tk

end Mathlib.Tactic.Hint
