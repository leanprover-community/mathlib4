module

public import Mathlib.Tactic.ClickSuggestions.TryPremises
public import Mathlib.Tactic.ClickSuggestions.Unfold
public import Mathlib.Tactic.Widget.Conv
public meta import Mathlib.Lean.Meta.KAbstractPositions

/-!
# Point & click suggestions

This file defines `#click_suggestions`, a command that enables an interactive interface that
gives lemma/tactic suggestions for any expression selected by the user.

The library search uses a (lazy) `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas.
It excludes lemmas that are automatically generated.
Each lemma is then checked one by one (in parallel) to see whether it is applicable.
For each lemma that works, the corresponding `rw`/`apply`/`apply at`/`grw` tactic is constructed,
so that it can be pasted into the editor when selected by the user.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections. The sections are ordered by this score.
Within each section, the lemmas are sorted by
- lemmas with fewer extra goals come first
- left-to-right rewrites come before right-to-left rewrites
- shorter lemma names come first
- shorter replacement expressions come first (when taken as a string)
- alphabetically ordered by lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

## TODO

- Improve the logic around `nth_rw` and occurrences.
- It may be possible to have integrated support for creating sequences of `calc` blocks,
  using the suggested rewrites.

-/
meta section

namespace Mathlib.Tactic.ClickSuggestions
open Lean Meta Server Widget ProofWidgets Jsx

open RefreshComponent

def viewKAbstractSubExpr' {m α}
    [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadError m]
    (e : Expr) (pos : SubExpr.Pos) (k : Expr → RwKind → m α) : m α := do
  if let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr e pos then
    let tpCorrect ← kabstractIsTypeCorrect e subExpr pos
    k subExpr (.valid tpCorrect occ)
  else
    Meta.viewSubexpr (fun _ e ↦ k e .hasBVars) pos e

public def generateSuggestions (loc : SubExpr.GoalsLocation)
    (parentDecl? : Option Name) (token : RefreshToken) : clickSuggestionsM Unit := do
  -- TODO: instead of just putting `✝` after inaccessible names,
  -- we should figure out how to use `rename_i` to actually refer to shadowed local variables.
  let lctx := (← getLCtx) |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx' lctx do
  -- Pre-emptively instantiate all metavariables, to avoid annoying issues later on.
  instantiateMVarDeclMVars loc.mvarId
  trackingComputation "click_suggestions" do
  let (fvarId?, pos) ← match loc.loc with
    | .hypType fvarId pos  => pure (some fvarId, pos)
    | .target pos => pure (none, pos)
    | .hyp _fvarId =>
      -- In a follow-up PR: suggestions for `induction`/`cases`, `contrapose`
      return
    | .hypValue .. =>
      token.update <| .text "internal click_suggestions error: selected location is a `.hypValue`"
      return
  let rootExpr ← match fvarId? with
    | some fvarId => fvarId.getType
    | none => loc.mvarId.getType
  -- TODO: instead of computing the occurrences a single time (i.e. the `n` in `nth_rw n`),
  -- compute the occurrence for each suggestion separately, to avoid inaccuracies.
  viewKAbstractSubExpr' rootExpr pos fun subExpr rwKind ↦ do
  let mut htmls : Array Html := #[]

  -- In a follow-up PR: suggestions for
  -- `induction`/`cases`, `contrapose`, if `subExpr` is an fvar.
  -- `rfl`, `intro`, `by_contra`
  -- `push`, `simp`, `norm_cast`, `ring`/`field`/`abel`/..

  if let some html ← suggestUnfold subExpr rwKind then
    markProgress
    htmls := htmls.push html

  let (searchHtml, token') ← mkRefreshComponent
  htmls := htmls.push searchHtml
  token.update (.element "div" #[("style", json% {"marginLeft" : "4px"})] htmls)

  librarySearchSuggestions rootExpr subExpr rwKind parentDecl? token'

/-- If the set of computations is non-empty, display a `⏳` symbol with hover information that
shows all of the ongoing computations. -/
private def rerenderStatus (computations : Std.HashMap String Nat) : Html :=
  if computations.isEmpty then
    .text ""
  else
    -- TODO: use a fancier throbber instead of `⏳`?
    let title := String.intercalate ", " computations.keys;
    <span title={title}> {.text "⏳"} </span>

@[server_rpc_method]
public def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let some loc := props.selectedLocations.back? | return .text ""
  let doc ← RequestM.readDoc
  if loc.loc matches .hypValue .. then
    return .text "click_suggestions cannot suggest anything about the value of a let variable."
  let some onGoal := props.goals.findFinIdx? (·.mvarId == loc.mvarId) |
    return .text "click_suggestions: please reload the tactic state"
  let goal := props.goals[onGoal]
  let onGoal := guard (onGoal.val != 0) *> some onGoal.val
  let some goalsAt := (FileWorker.findGoalsAt? doc (doc.meta.text.lspPosToUtf8Pos props.pos)).get |
    return .text "Internal click_suggestions error: could not find any goal at the cursor position"
  let some { ctxInfo := { parentDecl?, .. }, tacticInfo := { stx, .. }, .. } :=
    goalsAt.find? fun { useAfter, tacticInfo, .. } ↦
      let goals := if useAfter then tacticInfo.goalsAfter else tacticInfo.goalsBefore
      goals.contains loc.mvarId
    | return .text "click_suggestions: Please reload the tactic state"
  goal.ctx.val.runMetaM {} do loc.mvarId.withContext do
    let (statusHtml, statusToken) ← mkRefreshComponent
    let targetHtml ←
      if let .hyp h := loc.loc then
        pure <span> hypothesis {← exprToHtml (.fvar h)} </span>
      else
        Meta.viewSubexpr (fun _ e ↦ exprToHtml e) loc.pos (← loc.rootExpr)
    let html ← mkRefreshComponentM
      (.text "click_suggestions has started searching.") fun masterToken ↦ do
      (generateSuggestions loc parentDecl? masterToken).run {
        onGoal, stx, masterToken, statusToken
        «meta» := doc.meta
        cursorPos := props.pos
        progress? := ← IO.mkRef false
        goal := loc.mvarId
        hyp? := loc.fvarId?
        pos := loc.pos
      } |>.run' {}
    return <details «open»={true}>
      <summary className="mv2 pointer">
        click_suggestions suggestions for {targetHtml}: {statusHtml}
      </summary>
      {html}
    </details>

/-- The component called by the `#click_suggestions` command. -/
@[widget_module]
public def clickSuggestionsComponent : Component PanelWidgetProps :=
  mk_rpc_widget% rpc

elab "#click_suggestions" : command => do
  let widget ← Elab.Command.liftCoreM <|
    WidgetInstance.ofHash clickSuggestionsComponent.javascriptHash (return json% {})
  addPanelWidgetLocal widget

end Mathlib.Tactic.ClickSuggestions
