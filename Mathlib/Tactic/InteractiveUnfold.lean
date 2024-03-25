/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Std.Lean.Position
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Lean.Meta.KAbstractPositions

open Lean Meta Server Widget ProofWidgets Jsx


/-- The `Expr` at a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.rootExpr : SubExpr.GoalsLocation → MetaM Expr
  | ⟨_, .hyp fvarId⟩        => fvarId.getType
  | ⟨_, .hypType fvarId _⟩  => fvarId.getType
  | ⟨_, .hypValue fvarId _⟩ => do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩     => mvarId.getType

/-- The `SubExpr.Pos` of a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.pos : SubExpr.GoalsLocation → SubExpr.Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos


/-- Reduction function for the `unfold'` tactic. -/
def unfold (e : Expr) : MetaM Expr := do
  /- β-reduction -/
  if e.isHeadBetaTarget then
    return e.withAppRev Expr.betaRev
  /- η-reduction -/
  if let some e := e.etaExpandedStrict? then
    return e
  /- ζ-reduction -/
  if let .letE _ _ v b _ := e then
    return b.instantiate1 v
  /- projection reduction -/
  if let some e ← reduceProj? e then
    return e.headBeta
  if let .const n _ := e.getAppFn then
    if ← isProjectionFn n then
      if let some e ← unfoldDefinition? e then
        if let some r ← reduceProj? e.getAppFn then
          return mkAppN r e.getAppArgs |>.headBeta
  /- unfolding a let-bound free variable -/
  if let .fvar fvarId := e.getAppFn then
    if let some value ← fvarId.getValue? then
      return value.betaRev e.getAppRevArgs
  /- unfolding a constant -/
  if let some e ← unfoldDefinition? e then
    return e

  throwError m! "Could not find a definition for {e}."


partial def unfolds (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  try
    let e ← unfold e
    unfolds e (acc.push e)
  catch _ =>
    return acc


def printToPaste (e : Expr) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.unicode.fun true) do
  return Format.pretty (← Meta.ppExpr e)

def getDefinitions (loc : SubExpr.GoalsLocation) :
    ExceptT Html MetaM (Array (CodeWithInfos × String)) := do
  let e ← loc.rootExpr
  let subExpr ← Core.viewSubexpr loc.pos e
  if subExpr.hasLooseBVars then
    throwThe Html $ .text "rw doesn't work on expressions with bound variables."

  let replacements ← unfolds subExpr

  let positions ← kabstractPositions subExpr e
  let cfg := if positions.size == 1 then "" else
    match positions.findIdx? (· == loc.pos) with
    | some n => s! " (config := \{ occs := .pos [{n+1}] })"
    | none => ""
  let location ← (do match loc.loc with
    | .hyp fvarId
    | .hypType fvarId _ => return s! " at {← fvarId.getUserName}"
    | _ => return "")
  let lhs ← printToPaste subExpr

  let mut results := #[]
  let mut forbidden : HashSet String := HashSet.empty.insert lhs
  for d in replacements do
    let rhs ← printToPaste d
    unless forbidden.contains rhs do
      forbidden := forbidden.insert rhs
      results := results.push
        (← ppExprTagged d, s! "rw{cfg} [show {lhs} = {rhs} from rfl]{location}")

  if results.isEmpty then
    throwThe Html
      <span>
        could not find a definition for {<InteractiveCode fmt={← ppExprTagged subExpr}/>}
      </span>

  return results

def renderDefinitions (defs : Array (CodeWithInfos × String)) (range : Lsp.Range)
    (doc : FileWorker.EditableDocument) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">
      {.text "Definitional rewrites:"}
    </summary>
    {
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
      defs.map fun (replacement, tactic) =>
        <li> {
        .element "p" #[] <|
          #[<span className="font-code"> {
            Html.ofComponent MakeEditLink
              (.ofReplaceRange doc.meta range tactic)
              #[.text replacement.stripTags] }
          </span>] }
        </li> }
  </details>


@[server_rpc_method_cancellable]
def InteractiveUnfold.rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "unfold?: Please shift-click an expression."
  if loc.loc matches .hypValue .. then
    return .text "unfold? doesn't work on the value of a let-bound free variable."
  let some goal := props.goals[0]? |
    return .text "There is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "The selected expression should be in the main goal."
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      match ← getDefinitions loc with
      | .error msg  => return msg
      | .ok results =>
        if results.isEmpty then
          return .text ""
        return renderDefinitions results props.replaceRange doc


@[widget_module]
def InteractiveUnfold : Component SelectInsertParams :=
  mk_rpc_widget% InteractiveUnfold.rpc


/-- Unfold the selected expression in one of the following ways:

- β-reduction: `(fun x₁ .. xₙ => t[x₁, .., xₙ]) a₁ .. aₙ` → `t[a₁, .., aₙ]`
- η-reduction: `fun x₁ .. xₙ => f x₁ .. xₙ` → `f`
- ζ-reduction: `let a := v; t[a]` → `t[v]`
- projection reduction: `instAddNat.1 a b` → `Nat.add a b`
- unfolding a constant or a let-bound free variable: `Surjective f` → `∀ b, ∃ a, f a = b`

To use `unfold?`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `unfols?` by a tactic that performs this rewrite.

 -/
elab stx:"unfold?" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash InteractiveUnfold.javascript)
    (pure $ json% { replaceRange : $range }) stx
