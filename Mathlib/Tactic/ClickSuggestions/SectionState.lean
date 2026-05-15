/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.Util
public import ProofWidgets.Component.FilterDetails

/-!
# Infrastructure for searching and displaying sets of lemmas

This is used for `apply`, `apply at`, `rw` and `grw` suggestions.
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions
open Lean Widget ProofWidgets Jsx

variable {α : Type} [Ord α] [Inhabited α]

/-- `Result` stores the information from a lemma that was successfully applied. -/
structure Result (α : Type) where
  /-- `filtered` will be shown in the filtered view. -/
  filtered : Option Html
  /-- `unfiltered` will be shown in the unfiltered view. -/
  unfiltered : Html
  /-- `key` is used for sorting and comparing theorems. -/
  key : α
  /-- The `pattern` of the first lemma in a section is shown as the header of that section. -/
  pattern : Html
deriving Inhabited

instance [Ord α] : Ord (Result α) := ⟨(compare ·.key ·.key)⟩
instance [Ord α] : LT (Result α) := ltOfOrd

/-! ### Maintaining the state of the widget -/

structure SectionState (α : Type) where
  /-- The results of the theorems that successfully applied. -/
  results : Array (Result α) := #[]
  /-- The results of the theorems that threw an error when trying to apply them. -/
  errors : Array Html := #[]
  -- TODO: add a field for ongoing computations.
  deriving Nonempty

/-- Insert the new result `res` into the array `arr` of already existing results.

We maintain the invariants that `results` is sorted, and for each set of duplicate results,
only the first one can have the `filtered` field set to `some`. -/
@[specialize]
def Result.insertInArray (res : Result α) (arr : Array (Result α)) (isDup : α → α → MetaM Bool) :
    MetaM (Array (Result α)) := do
  if let some idx ← findDuplicate res arr then
    if res < arr[idx]! then
      return (arr.modify idx ({ · with filtered := none })).binInsert (· < ·) res
    else
      return arr.binInsert (· < ·) { res with filtered := none }
  else
    return arr.binInsert (· < ·) res
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : Result α) (results : Array (Result α)) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      try
        pure res.filtered.isSome <&&> isDup res.key result.key
      catch _ =>
        pure false

def SectionState.insertResult (s : SectionState α) (res : Result α)
    (isDup : α → α → MetaM Bool) : MetaM (SectionState α) := do
  let { results, errors } := s
  let results ← fun c₁ c₂ c₃ c₄ ↦
    (res.insertInArray results isDup c₁ c₂ c₃ c₄).catchExceptions fun ex ↦ do
    if let .internal id _ := ex then
      if id == interruptExceptionId then
        return default
    panic! s!"an error occurred when checking for duplicate entries:\n{← ex.toMessageData.toString}"
  return { results, errors }

def SectionState.pushError (s : SectionState α) (error : Html) : SectionState α :=
  let { results , errors } := s
  { results, errors := errors.push error }

def renderErrors (errors : Array Html) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">
      <span «class»="error"> Failures: </span>
    </summary>
    {Html.element "ul" #[("style", json% { "padding-left" : "30px"})] errors}
  </details>

inductive SectionKind where
  | hyp | currFile | imported

-- TODO?: add a `⏳️` with hover info that shows which lemmas are still being computed?
def renderSection {α} (tactic : String) (kind : SectionKind) (s : SectionState α) : Html :=
  Id.run do
  let { results, errors } := s
  if results.isEmpty && errors.isEmpty then
    return .text ""
  let head := if let some head := results[0]? then head.pattern else .text ""
  let mut all := .element "div" #[] <| results.map (·.unfiltered)
  let mut filtered := .element "div" #[] <| results.filterMap (·.filtered)
  unless errors.isEmpty do
    all := <div> {all} {renderErrors errors} </div>
    filtered := <div> {filtered} {renderErrors errors} </div>
  let suffix := match kind with
    | .hyp => " (local hypotheses)"
    | .currFile => " (current file)"
    | .imported => ""
  let header := <span> {.text s!"{tactic}: "} {head} {.text suffix} </span>
  -- Don't apply any filter to local results.
  unless kind matches .imported do
    return <details «open»={true}> <summary> {header} </summary> {all} </details>
  return <FilterDetails summary={header} all={all} filtered={filtered} initiallyFiltered={true} />

/-- Spawn a task that computes a piece of `Html` to be displayed when finished. -/
@[specialize]
def spawnTask {α} (premise : Premise) (k : clickSuggestionsM α) :
    clickSuggestionsM <| Task (Except Html (Option α)) := do
  let premiseHtml ← premise.toHtml
  let act ← saveCtxM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
    to use `withCurrHeartbeats` to avoid stray maxHeartbeats errors. -/
    withCurrHeartbeats do
      try
        return .ok (some (← k))
      catch ex =>
        /- By default, we catch the errors from failed lemma applications
        (appart from runtime exceptions, i.e. max heartbeats or max recursion depth,
        which aren't caught by the `try`-`catch` block).
        The `click_suggestions.debug` option allows the user to still see all errors. -/
        if click_suggestions.debug.get (← getOptions) then
          throw ex
        return .ok none
  BaseIO.asTask <| act.catchExceptions fun ex =>
    return .error <li>
        {premiseHtml} failed:
        <br/>
        <InteractiveMessage msg={← Server.WithRpcRef.mk ex.toMessageData} />
      </li>

end Mathlib.Tactic.ClickSuggestions
