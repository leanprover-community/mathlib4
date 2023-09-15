import Lean.Meta.ExprLens
import ProofWidgets.Data.Html
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod

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

structure SelectionPanelProps extends PanelWidgetProps where
  /-- The range in the source document where the `gcongr` command will be inserted. -/
  replaceRange : Lsp.Range
  deriving RpcEncodable

open scoped Jsx in
def mkSelectionPanelRPC
    (mkCmdStr : (pos : Array Lean.SubExpr.GoalsLocation) → (goalType : Expr) → MetaM String)
    (helpMsg: String) (title: String) (props : SelectionPanelProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let inner : Html ← (do
      if props.selectedLocations.isEmpty then
        return <span>{.text helpMsg}</span>
      let some selectedLoc := props.selectedLocations[0]? | unreachable!

      let some g := findGoalForLocation props.goals selectedLoc
        | throw $ .invalidParams
            s!"could not find goal for location {toJson selectedLoc}"
      g.ctx.val.runMetaM {} do
        let md ← g.mvarId.getDecl
        let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
        Meta.withLCtx lctx md.localInstances do
          let newCode ← mkCmdStr props.selectedLocations md.type
          return .ofComponent
            MakeEditLink
            (.ofReplaceRange doc.meta props.replaceRange newCode)
            #[ .text newCode ])
    return <details «open»={true}>
        <summary className="mv2 pointer">{.text title}</summary>
        <div className="ml1">{inner}</div>
      </details>
