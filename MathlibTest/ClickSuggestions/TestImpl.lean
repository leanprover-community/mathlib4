/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions
public import ProofWidgets.Component.HtmlDisplay

/-!
# Testing of `#click_suggestions`

It is hard to test `#click_suggestions` directly, because it emits HTML that the user interacts with.
Instead, we define a (scoped) command `click_test {pos} => "{tac}"`, which verifies that
if you do a `#click_suggestions` at position `pos`, `tac` will be one of the suggestions.
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta SubExpr ProofWidgets RefreshComponent Server

partial def getHtmlComponentProps {Props} [RpcEncodable Props] (html : Html) (c : Component Props)
    (arr : Array Props) : CoreM (Array Props) := do
  match html with
  | .element _ _ htmls => htmls.foldlM (fun arr html ↦ getHtmlComponentProps html c arr) arr
  | .text _ => return arr
  | .component hash _ lazy htmls =>
    let mut arr := arr
    if hash == c.javascriptHash then
      arr := arr.push <| ← getProps lazy
    if hash == FilterDetails.javascriptHash then
      let props : FilterDetailsProps ← getProps lazy
      arr ← getHtmlComponentProps props.all c arr
    if hash == RefreshComponent.javascriptHash then
      let props : RefreshComponent.Props ← getProps lazy
      arr ← getHtmlComponentProps (← getFinalHtml props.state.val) c arr
    htmls.foldlM (fun arr html ↦ getHtmlComponentProps html c arr) arr
where
  getProps {Props} [RpcEncodable Props] (lazy : LazyEncodable Json) :
      CoreM Props := do
    let (json, state) := lazy.run {}
    match rpcDecode json state with
    | .ok props => return props
    | .error e => throwError "An error occurred when looking at the HTML: {e}"
/- Wait until the state has finished refreshing, and the return the final HTML.
This is useful for inspecting `Html` from within Lean. -/
  getFinalHtml (info : RefreshRef) : BaseIO Html := do
  let { curr, next, .. } ← info.ref.get
  if next.get.isNone then
    return curr.get
  getFinalHtml info

def trimWhitespace (string : String) : String :=
  "\n".intercalate <| ((string.trimAscii.split '\n').map (·.trimAscii.toString)).toList

elab "click_test" hyp?:(ident)? pos?:(str)? "=>" expecteds:str+ : tactic =>
  Elab.Tactic.withMainContext do
  let hyp? ← hyp?.mapM fun hyp ↦ return (← getLocalDeclFromUserName hyp.getId).fvarId
  let pos? ← pos?.mapM fun pos ↦ do
    match Pos.fromString? pos.getString with
    | .ok pos => return pos
    | .error s => throwError "{s}"
  let expecteds := expecteds.map (·.getString)
  let loc : GoalLocation := ← match hyp?, pos? with
    | some h, some pos => pure <| .hypType h pos
    | none  , some pos => pure <| .target pos
    | some h, none     => pure <| .hyp h
    | none  , none     => pure <| .target .root
  let mvarId ← Elab.Tactic.getMainGoal
  let text ← getFileMap
  let some cursorPos := (← getRef).getPos? | throwError "found no valid cursor position"
  let cursorPos := text.utf8PosToLspPos cursorPos
  let (_, statusToken) ← mkRefreshComponent
  let (html, masterToken) ← mkRefreshComponent
  let ctx := {
    cursorPos, masterToken, statusToken
    «meta» := { (default : DocumentMeta) with text }
    onGoal := none
    stx := default
    progress? := ← IO.mkRef false
    goal := mvarId
    hyp?
    pos := pos?.getD .root
  }
  (generateSuggestions { loc, mvarId } none masterToken).run ctx |>.run' {}
  let props ← getHtmlComponentProps html MakeEditLink #[]
  let suggested := props.flatMap (·.edit.edits.map (trimWhitespace ·.newText))
  for expected in expecteds do
    let expected := trimWhitespace expected
    unless suggested.contains expected do
      Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return json% { html: $(← rpcEncode html) })
        (← getRef)
      throwError "{expected.quote} is not one of the suggestions: {suggested.map (·.quote)}"

end Mathlib.Tactic.ClickSuggestions
