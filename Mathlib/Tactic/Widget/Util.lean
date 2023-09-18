import Lean.Meta.ExprLens
import Lean.Elab.PreDefinition.Structural.SmartUnfolding

import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Data.Html
import ProofWidgets.Component.OfRpcMethod -- needed in all files using this one.

import Mathlib.Tactic.Widget.SelectInsertParamsClass

open Lean Meta Server

def Lean.SubExpr.GoalLocation.target! : Lean.SubExpr.GoalLocation → SubExpr.Pos
| .target pos => pos
| _ => panic! "You must select part of the goal."

def insertMetaVar (e : Expr) (pos  : SubExpr.Pos) : MetaM Expr :=
replaceSubexpr (fun _ ↦  do mkFreshExprMVar none .synthetic) pos e

def String.renameMetaVar (s : String) : String :=
  match s.splitOn "?m." with
  | [] => ""
  | [s] => s
  | head::tail => head ++ "?_" ++ "?_".intercalate (tail.map fun s ↦ s.dropWhile Char.isDigit)

open ProofWidgets

def findGoalForLocation (goals : Array Widget.InteractiveGoal) (loc : SubExpr.GoalsLocation) :
    Option Widget.InteractiveGoal :=
  goals.find? (·.mvarId == loc.mvarId)

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


open scoped Jsx in open SelectInsertParamsClass in
def mkSelectionPanelRPC {Params : Type} [SelectInsertParamsClass Params]
  (mkCmdStr : (pos : Array Lean.SubExpr.GoalsLocation) → (goalType : Expr) → Params → MetaM (String × String))
  (helpMsg : String) (title : String) (params : Params) : RequestM (RequestTask Html) :=
RequestM.asTask do
  let doc ← RequestM.readDoc
  let inner : Html ← (do
    if (selectedLocations params).isEmpty then
      return <span>{.text helpMsg}</span>
    let some selectedLoc := (selectedLocations params)[0]? | unreachable!

    let some g := findGoalForLocation (goals params) selectedLoc
      | throw $ .invalidParams
          s!"could not find goal for location {toJson selectedLoc}"
    g.ctx.val.runMetaM {} do
      let md ← g.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        let (linkText, newCode) ← mkCmdStr (selectedLocations params) md.type params
        return .ofComponent
          MakeEditLink
          (.ofReplaceRange doc.meta (replaceRange params) newCode)
          #[ .text linkText ])
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1">{inner}</div>
    </details>
