/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Lean.Meta.ExprLens
import Lean.Elab.PreDefinition.Structural.SmartUnfolding

import Std.Data.Nat.Init.Lemmas

import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod -- needed in all files using this one.

import Mathlib.Tactic.Widget.SelectInsertParamsClass

open Lean Meta Server

open Lean.SubExpr in
def getGoalLocations (locations : Array GoalsLocation) : Array SubExpr.Pos := Id.run do
  let mut res := #[]
  for location in locations do
    if let .target pos := location.loc then
      res := res.push pos
  return res

def insertMetaVar (e : Expr) (pos  : SubExpr.Pos) : MetaM Expr :=
replaceSubexpr (fun _ ↦  do mkFreshExprMVar none .synthetic) pos e

def String.renameMetaVar (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++ "?_".intercalate (tail.map fun s ↦ s.dropWhile Char.isDigit)

open ProofWidgets

/-- Structures providing parameters for a Select and insert widget. -/
structure SelectInsertParams where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  /-- The range in the source document where the command will be inserted. -/
  replaceRange : Lsp.Range
  deriving SelectInsertParamsClass, RpcEncodable

/- TODO: Find where this lemma hides. -/
theorem Array.size_pos {α: Type _} {a : Array α} (h : ¬ a.isEmpty) : 0 < a.size := by
  erw [decide_eq_true_eq] at h
  exact Nat.pos_of_ne_zero h

open scoped Jsx in open SelectInsertParamsClass Lean.SubExpr in
/-- Helper function to create a widget allowing to select parts of the main goal
and then display a link that will insert some tactic call.

The main argument is `mkCmdStr` which is a function creating the link text and the tactic call text.
The `helpMsg` argument is displayed when nothing is selected and `title` is used as a panel title.
The `onlyGoal` argument says whether the selected has to be in the goal. Otherwise it
can be in the local context.
The `onlyOne` argument says whether one should select only one sub-expression.
In every cases, all selected subexpressions should be in the main goal or its local context.

The last arguments `params` should not be provided so that the output
has type `Params → RequestM (RequestTask Html)` and can be fed to the `mk_rpc_widget%`
elaborator.

Note that the `pos` and `goalType` arguments to `mkCmdStr` could be extracted for the `Params`
argument but that extraction would happen in every example, hence it is factored out here.
We also make sure `mkCmdStr` is executed in the right context.
 -/
def mkSelectionPanelRPC {Params : Type} [SelectInsertParamsClass Params]
  (mkCmdStr : (pos : Array GoalsLocation) → (goalType : Expr) → Params → MetaM (String × String))
  (helpMsg : String) (title : String) (onlyGoal := true) (onlyOne := false) :
  (params : Params) → RequestM (RequestTask Html) :=
fun params ↦ RequestM.asTask do
let doc ← RequestM.readDoc
if h : (goals params).isEmpty then
    return <span>{.text "There is no goal to solve!"}</span> -- This shouldn't happen.
else
  let mainGoal := (goals params)[0]'(Array.size_pos h)
  let mainGoalName := mainGoal.mvarId.name
  let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
  let be_where := if onlyGoal then "in the main goal." else "in the main goal or its context."
  let errorMsg := s!"{all} should be {be_where}"
  let inner : Html ← (do
    if onlyOne && (selectedLocations params).size > 1 then
      return <span>{.text "You should select only one sub-expression"}</span>
    for selectedLocation in selectedLocations params do
      if selectedLocation.mvarId.name != mainGoalName then
        return <span>{.text errorMsg}</span>
      else if onlyGoal then
        if !(selectedLocation.loc matches (.target _)) then
          return <span>{.text errorMsg}</span>
    if (selectedLocations params).isEmpty then
      return <span>{.text helpMsg}</span>
    mainGoal.ctx.val.runMetaM {} do
      let md ← mainGoal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        let (linkText, newCode) ← mkCmdStr (selectedLocations params) md.type.consumeMData params
        return .ofComponent
          MakeEditLink
          (.ofReplaceRange doc.meta (replaceRange params) newCode)
          #[ .text linkText ])
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1">{inner}</div>
    </details>
