import Mathlib.Util.InfoTree.Basic

namespace Lean.Elab

structure InfoTreeNode (α : Type) where
  node : α
  children : List Json
deriving ToJson

structure TacticInfo.Json where
  stx : String
  goalsBefore : List String
  goalsAfter : List String
deriving ToJson

-- Note: this is not responsible for converting the children to Json.
def TacticInvocation.toJson (i : TacticInvocation) : IO Json := do
  return Lean.toJson (
    { stx := Format.pretty (← i.pp),
      goalsBefore := (← i.goalState).map Format.pretty,
      goalsAfter := (← i.goalStateAfter).map Format.pretty } : TacticInfo.Json)

structure CommandInfo.Json where
  elaborator : Name
  stx : String
deriving ToJson

def CommandInfo.toJson (info : CommandInfo) (ctx : ContextInfo) : IO Lean.Json := do
  return Lean.toJson (
    { elaborator := info.elaborator,
      stx := (← ctx.ppSyntax {} info.stx).pretty } : CommandInfo.Json)

structure TermInfo.Json where
  elaborator : Name
  stx : String
  expectedType? : Option String
  expr : String
  isBinder : Bool
deriving ToJson

def TermInfo.toJson (info : TermInfo) (ctx : ContextInfo) : IO Lean.Json := do
  return Lean.toJson (
    { elaborator := info.elaborator,
      stx := (← ctx.ppSyntax {} info.stx).pretty,
      expectedType? := ← info.expectedType?.mapM fun ty => do pure (← ctx.ppExpr ty).pretty
      expr := (← ctx.ppExpr info.expr).pretty
      isBinder := info.isBinder } : TermInfo.Json)

structure InfoTree.HoleJson where
  goalState : String
deriving ToJson

structure InfoTree.MissingJson where
  kind : String
deriving ToJson

partial def InfoTree.toJson (t : InfoTree) (ctx? : Option ContextInfo) : IO Json := do
  match t with
  | .context i t => t.toJson i
  | .node info children =>
    if let some ctx := ctx? then
      let node : Json ← match info with
      | .ofTacticInfo         info => TacticInvocation.toJson ⟨info, ctx, children⟩
      | .ofTermInfo           info => info.toJson ctx
      | .ofCommandInfo        info => info.toJson ctx
      | .ofMacroExpansionInfo _    => return Lean.toJson (InfoTree.MissingJson.mk "MacroExpansionInfo")
      | .ofOptionInfo         _    => return Lean.toJson (InfoTree.MissingJson.mk "OptionInfo")
      | .ofFieldInfo          _    => return Lean.toJson (InfoTree.MissingJson.mk "FieldInfo")
      | .ofCompletionInfo     _    => return Lean.toJson (InfoTree.MissingJson.mk "CompletionInfo")
      | .ofUserWidgetInfo     _    => return Lean.toJson (InfoTree.MissingJson.mk "UserWidgetInfo")
      | .ofCustomInfo         _    => return Lean.toJson (InfoTree.MissingJson.mk "CustomInfo")
      | .ofFVarAliasInfo      _    => return Lean.toJson (InfoTree.MissingJson.mk "FVarAliasInfo")
      | .ofFieldRedeclInfo    _    => return Lean.toJson (InfoTree.MissingJson.mk "FieldRedeclInfo")
      return Lean.toJson (InfoTreeNode.mk node (← children.toList.mapM fun t' => t'.toJson ctx))
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
     return Lean.toJson (InfoTree.HoleJson.mk (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty)
    else throw <| IO.userError "No `ContextInfo` available."

end Lean.Elab
