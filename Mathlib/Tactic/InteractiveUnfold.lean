/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean
import Std.Lean.Position
import Std.Lean.Name
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Lean.SubExpr
import Mathlib.Lean.Meta.KAbstractPositions

/-! # Interactive unfolding -/

open Lean Meta Server Widget ProofWidgets Jsx

namespace Mathlib.Tactic.InteractiveUnfold

/-- same as `unfoldDefinition?`, except it handles well founded recursive definitions better. -/
def unfold? (e : Expr) : MetaM (Option Expr) := do
  if let .const n lvls := e.getAppFn then
    /- unfolding a constant defined with well founded recursion -/
    if let some info := Elab.WF.eqnInfoExt.find? (← getEnv) n then
      if info.levelParams.length == lvls.length then
        return (info.value.instantiateLevelParams info.levelParams lvls).beta e.getAppArgs
    /- unfolding any other constant -/
    else if let some e ← unfoldDefinition? e then
      return e
  return none

/-- Return the consecutive unfoldings of `e`. -/
partial def unfolds (e : Expr) : MetaM (Array Expr) := do
  let e' ← whnfCore e
  go e' (if e == e' then #[] else #[e'])
where
  /-- Append the unfoldings of `e` to `acc`. Assume `e` is in `whnfCore` form. -/
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    withCatchingRuntimeEx do
    try
      withoutCatchingRuntimeEx do withIncRecDepth do
      if let some e ← reduceNat? e then
        return #[e]
      if let some e ← reduceNative? e then
        return #[e]
      if let some e ← unfold? e then
        -- Note: whnfCore can give a recursion depth error
        let e ← whnfCore e
        return ← go e (acc.push e)
      return acc
    catch _ =>
      return acc

/-- Return `true` if `e` doesn't contain any internal functions. -/
def isUserFriendly (e : Expr) : Bool :=
  !e.foldConsts (init := false) (fun name => (· || name.isInternalDetail))

/-- Return the consecutive unfoldings of `e` that are user friendly. -/
def filteredUnfolds (e : Expr) : MetaM (Array Expr) :=
  return (← unfolds e).filter isUserFriendly

end InteractiveUnfold

/-- Return the rewrite tactic string `rw (config := ..) [← ..] at ..` -/
def mkRewrite (occ : Option Nat) (symm : Bool) (rewrite : String)
    (loc : Option Name) : String :=
  let cfg := match occ with
    | some n => s! " (config := \{ occs := .pos [{n}]})"
    | none => ""
  let loc := match loc with
    | some n => s! " at {n}"
    | none => ""
  let symm := if symm then "← " else ""
  s! "rw{cfg} [{symm}{rewrite}]{loc}"

/-- Return a string representation of the expression suitable for pasting into the editor. -/
def PasteString (e : Expr) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.match false
    |>.setBool `pp.unicode.fun true) do
  return Format.pretty (← Meta.ppExpr e) (width := 90) (indent := 2)

namespace InteractiveUnfold

/-- Return the unfolds from `unfolds` together with the tactic strings that do the unfoldings. -/
def unfoldsWithTacticString (e : Expr) (occ : Option Nat) (loc : Option Name) :
    MetaM (Array (Expr × String)) := do
  let replacements ← filteredUnfolds e
  let mut results := #[]
  let mut forbidden := HashSet.empty.insert s! "show {← PasteString (← mkEq e e)} from rfl"
  for replacement in replacements do
    let rfl := s! "show {← PasteString (← mkEq e replacement)} from rfl"
    unless forbidden.contains rfl do
      forbidden := forbidden.insert rfl
      results := results.push (replacement, mkRewrite occ false rfl loc)
  return results

/-- Render the unfolds of `e` as given by `filteredUnfolds`, with buttons at each suggestion
for pasting the rewrite tactic. -/
def renderDefinitions (e : Expr) (occ : Option Nat) (loc : Option Name) (range : Lsp.Range)
    (doc : FileWorker.EditableDocument) : MetaM (Option Html) := do
  let results ← unfoldsWithTacticString e occ loc
  if results.isEmpty then
    return none
  let core ← results.mapM fun (replacement, tactic) => do
    return <li> {
      .element "p" #[] <|
        #[<span className="font-code" style={json% { "white-space" : "pre-wrap" }}> {
          Html.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta range tactic)
            #[.text $ Format.pretty $ (← Meta.ppExpr replacement)] }
        </span>]
      } </li>
  return <details «open»={true}>
    <summary className="mv2 pointer">
      {.text "Definitional rewrites:"}
    </summary>
    {.element "ul" #[("style", json% { "padding-left" : "30px"})] core}
  </details>


@[server_rpc_method_cancellable]
private def rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
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

      let some (subExpr, occ) ← viewKAbstractSubExpr (← loc.rootExpr) loc.pos |
        return .text "rw doesn't work on expressions with bound variables."
      let html ← renderDefinitions subExpr occ (← loc.location) props.replaceRange doc
      return html.getD
        <span>
          could not find a definition for {<InteractiveCode fmt={← ppExprTagged subExpr}/>}
        </span>

/-- The component called by the `unfold?` tactic -/
@[widget_module]
def UnfoldComponent : Component SelectInsertParams :=
  mk_rpc_widget% InteractiveUnfold.rpc


/-- Unfold the selected expression any number of times.
- After each unfold?, we apply `whnfCore` to simplify the expression.
- Explicit natural number expressions are evaluated.
- The results of class projections marked with `@[default_instance]` are skipped.
  This is relevant for notational type classes like `+`: we don't want to suggest `Add.add a b`
  as an unfolding of `a + b`.

To use `unfold?`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `unfold?` by a tactic that performs this rewrite.
-/
elab stx:"unfold?" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash UnfoldComponent.javascript)
    (pure $ json% { replaceRange : $range }) stx
