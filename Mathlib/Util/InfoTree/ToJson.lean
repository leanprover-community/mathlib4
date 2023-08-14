import Mathlib.Util.InfoTree.TacticInvocation

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
def TacticInvocation.toJson (i : TacticInvocation) : IO Json := do
  return Lean.toJson (
    { name := i.info.name?
      stx :=
      { pp := Format.pretty (← i.pp),
        -- raw := toString i.info.stx,
        range := i.info.stx.toRange i.ctx },
      goalsBefore := (← i.goalState).map Format.pretty,
      goalsAfter := (← i.goalStateAfter).map Format.pretty } : TacticInfo.Json)

structure CommandInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
deriving ToJson

def CommandInfo.toJson (info : CommandInfo) (ctx : ContextInfo) : IO Lean.Json := do
  return Lean.toJson (
    { elaborator := match info.elaborator with | .anonymous => none | n => some n,
      stx := ← info.stx.toJson ctx {} } : CommandInfo.Json)

structure TermInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
  expectedType? : Option String
  expr : String
  isBinder : Bool
deriving ToJson

def TermInfo.toJson (info : TermInfo) (ctx : ContextInfo) : IO Lean.Json := do
  return Lean.toJson (
    { elaborator := match info.elaborator with | .anonymous => none | n => some n,
      stx := ← info.stx.toJson ctx info.lctx,
      expectedType? := ← info.expectedType?.mapM fun ty => do
        pure (← ctx.ppExpr info.lctx ty).pretty
      expr := (← ctx.ppExpr info.lctx info.expr).pretty
      isBinder := info.isBinder } : TermInfo.Json)

structure InfoTree.HoleJson where
  goalState : String
deriving ToJson

partial def InfoTree.toJson (t : InfoTree) (ctx? : Option ContextInfo) : IO Json := do
  match t with
  | .context i t => t.toJson i
  | .node info children =>
    if let some ctx := ctx? then
      let node : Option Json ← match info with
      | .ofTacticInfo  info => some <$> TacticInvocation.toJson ⟨info, ctx, children⟩
      | .ofTermInfo    info => some <$> info.toJson ctx
      | .ofCommandInfo info => some <$> info.toJson ctx
      | _                   => pure none
      return Lean.toJson (InfoTreeNode.mk info.kind node (← children.toList.mapM fun t' => t'.toJson ctx))
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
     return Lean.toJson (InfoTree.HoleJson.mk (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty)
    else throw <| IO.userError "No `ContextInfo` available."

end Lean.Elab
