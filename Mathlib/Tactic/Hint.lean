/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Meta.Tactic.TryThis
import Batteries.Linter.UnreachableTactic
import Batteries.Control.Nondet.Basic
import Mathlib.Init

/-!
# The `hint` tactic.

The `hint` tactic tries the kitchen sink:
it runs every tactic registered via the `register_hint <prio> tac` command
on the current goal, and reports which ones succeed.

## Future work
It would be nice to run the tactics in parallel.
-/

open Lean Elab Tactic

open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Hint

/-- An environment extension for registering hint tactics with priorities. -/
initialize hintExtension :
    SimplePersistentEnvExtension (Nat × TSyntax `tactic) (List (Nat × TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Register a new hint tactic. -/
def addHint (prio : Nat) (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hintExtension.addEntry env (prio, stx)

/-- Return the list of registered hint tactics. -/
def getHints : CoreM (List (Nat × TSyntax `tactic)) :=
  return hintExtension.getState (← getEnv)

open Lean.Elab.Command in
/--
Register a tactic for use with the `hint` tactic, e.g. `register_hint 1000 simp_all`.
The numeric argument specifies the priority: tactics with larger priorities run before
those with smaller priorities. The priority must be provided explicitly.
-/
elab (name := registerHintStx)
    "register_hint" prio:num tac:tactic : command =>
    liftTermElabM do
  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
  let some prio := prio.raw.isNatLit?
    | throwError "expected a numeric literal for priority"
  addHint prio tac

initialize
  Batteries.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``registerHintStx

/--
Extracts the `MessageData` from the first clickable `Try This:` diff widget in the message.
Preserves (only) contexts and tags.
-/
private def getFirstTryThisFromMessage? : MessageData → Option MessageData
  | .ofWidget w msg => if w.id == ``Meta.Hint.tryThisDiffWidget then msg else none
  | .nest _ msg
  | .group msg => getFirstTryThisFromMessage? msg
  | .compose msg₁ msg₂ => getFirstTryThisFromMessage? msg₁ <|> getFirstTryThisFromMessage? msg₂
  | .withContext ctx msg => (getFirstTryThisFromMessage? msg).map <| .withContext ctx
  | .withNamingContext ctx msg => (getFirstTryThisFromMessage? msg).map <| .withNamingContext ctx
  | .tagged tag msg => (getFirstTryThisFromMessage? msg).map <| .tagged tag
  | .ofFormatWithInfos _ | .ofGoal _ | .trace .. | .ofLazy .. => none

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
  /-
  #adaptation_note 2025-08-27
  Suggestion styling was deprecated in lean4#9966.
  We use emojis for now instead.
  -/
  -- let style? := if goals.isEmpty then some .success else none
  let preInfo? := if goals.isEmpty then some "🎉 " else none
  let msg? : Option MessageData := msgs.toList.firstM (getFirstTryThisFromMessage? ·.data)
  let suggestion ← match msg? with
  | some m => pure <| SuggestionText.string (← m.toString)
  | none => pure <| SuggestionText.tsyntax tac
  return { preInfo?, suggestion, postInfo? }

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
Run all tactics registered using `register_hint`.
Print a "Try these:" suggestion for each of the successful tactics.

If one tactic succeeds and closes the goal, we don't look at subsequent tactics.
-/
-- TODO We could run the tactics in parallel.
-- TODO With widget support, could we run the tactics in parallel
--      and do live updates of the widget as results come in?
def hint (stx : Syntax) : TacticM Unit := withMainContext do
  let tacs := (← getHints).toArray.qsort (·.1 > ·.1) |>.toList.map (·.2)
  let tacs := Nondet.ofList tacs
  let results := tacs.filterMapM fun t : TSyntax `tactic => do
    if let some msgs ← observing? (withMessageLog (withoutInfoTrees (evalTactic t))) then
      if msgs.hasErrors then
        return none
      else
        return some (← getGoals, ← suggestion t msgs)
    else
      return none
  let results ← (results.toMLList.takeUpToFirst fun r => r.1.1.isEmpty).asArray
  let results := results.qsort (·.1.1.length < ·.1.1.length)
  addSuggestions stx (results.map (·.1.2))
  match results.find? (·.1.1.isEmpty) with
  | some r =>
    -- We don't restore the entire state, as that would delete the suggestion messages.
    setMCtx r.2.term.meta.meta.mctx
  | none => admitGoal (← getMainGoal)

/--
The `hint` tactic tries every tactic registered using `register_hint <prio> tac`,
and reports any that succeed.
-/
syntax (name := hintStx) "hint" : tactic

@[inherit_doc hintStx]
elab_rules : tactic
  | `(tactic| hint%$tk) => hint tk

end Mathlib.Tactic.Hint
