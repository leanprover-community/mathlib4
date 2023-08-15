import Mathlib.Util.InfoTree.TacticInvocation.Basic

/-!
# Exporting an `InfoTree` as Json

-/

namespace Lean.Elab

structure InfoTreeNode (α : Type) where
  kind : String
  node : Option α
  children : List Json
deriving ToJson

deriving instance ToJson for Lean.Position

structure Syntax.Range where
  synthetic : Bool
  start : Lean.Position
  finish : Lean.Position
deriving ToJson

structure Syntax.Json where
  pp : Option String
  -- raw : String
  range : Range
deriving ToJson

def _root_.Lean.Syntax.toRange (stx : Syntax) (ctx : ContextInfo) : Syntax.Range :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  { start := ctx.fileMap.toPosition pos
    finish := ctx.fileMap.toPosition endPos
    synthetic := match stx.getHeadInfo with
    | .original .. => false
    | _ => true }

def _root_.Lean.Syntax.toJson (stx : Syntax) (ctx : ContextInfo) (lctx : LocalContext) : IO Syntax.Json := do
  return {
    pp := match (← ctx.ppSyntax lctx stx).pretty with
      | "failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)" => none
      | pp => some pp
    -- raw := toString stx
    range := stx.toRange ctx }

structure TacticInfo.Json where
  name : Option Name
  stx : Syntax.Json
  goalsBefore : List String
  goalsAfter : List String
deriving ToJson

-- Note: this is not responsible for converting the children to Json.
def TacticInfo.toJson (i : TacticInfo) (ctx : ContextInfo) : IO TacticInfo.Json := do
  let I : TacticInvocation := ⟨i, ctx, .empty⟩
  return {
    name := i.name?
    stx :=
    { pp := Format.pretty (← I.pp),
      -- raw := toString i.info.stx,
      range := i.stx.toRange ctx },
    goalsBefore := (← I.goalState).map Format.pretty,
    goalsAfter := (← I.goalStateAfter).map Format.pretty }

structure CommandInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
deriving ToJson

def CommandInfo.toJson (info : CommandInfo) (ctx : ContextInfo) : IO CommandInfo.Json := do
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    stx := ← info.stx.toJson ctx {} }

structure TermInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
  expectedType? : Option String
  expr : String
  isBinder : Bool
deriving ToJson

def TermInfo.toJson (info : TermInfo) (ctx : ContextInfo) : IO TermInfo.Json := do
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    stx := ← info.stx.toJson ctx info.lctx,
    expectedType? := ← info.expectedType?.mapM fun ty => do
      pure (← ctx.ppExpr info.lctx ty).pretty
    expr := (← ctx.ppExpr info.lctx info.expr).pretty
    isBinder := info.isBinder }

structure InfoTree.HoleJson where
  goalState : String
deriving ToJson

partial def InfoTree.toJson (t : InfoTree) (ctx? : Option ContextInfo) : IO Json := do
  match t with
  | .context i t => t.toJson i
  | .node info children =>
    if let some ctx := ctx? then
      let node : Option Json ← match info with
      | .ofTermInfo    info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofCommandInfo info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofTacticInfo  info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | _                   => pure none
      return Lean.toJson (InfoTreeNode.mk info.kind node (← children.toList.mapM fun t' => t'.toJson ctx))
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
     return Lean.toJson (InfoTree.HoleJson.mk (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty)
    else throw <| IO.userError "No `ContextInfo` available."

end Lean.Elab
