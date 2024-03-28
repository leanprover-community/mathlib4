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

namespace Mathlib.Tactic

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

def printToPaste (e : Expr) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.match false
    |>.setBool `pp.unicode.fun true) do
  return Format.pretty (← Meta.ppExpr e) (indent := 2)

namespace InteractiveUnfold

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

/-- Return an array of consecutive unfoldings of `e`. -/
partial def unfolds (e : Expr) : MetaM (Array Expr) := do
  let e' ← whnfCore e
  go e' (if e == e' then #[] else #[e'])
where
  go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    if let some e ← reduceNat? e then
      return #[e]
    if let some e ← reduceNative? e then
      return #[e]
    if let some e ← unfold? e then
      -- whnfCore can give a recursion depth error, so we catch it
      withCatchingRuntimeEx do
      try
        withoutCatchingRuntimeEx do
        let e ← (whnfCore e)
        go e (acc.push e)
      catch _ =>
        return acc
    else
      return acc

def isUserFriendly (e : Expr) : Bool :=
  !e.foldConsts (init := false) (fun name bool => bool || name.isInternalDetail)

def filteredUnfolds (e : Expr) : MetaM (Array Expr) :=
  return (← unfolds e).filter isUserFriendly

/-- Return the unfolds from `unfolds` together with the tactic strings that do the unfoldings. -/
def unfoldsWithTacticString (e : Expr) (occ : Option Nat) (loc : Option Name) :
    MetaM (Array (Expr × String)) := do
  let replacements ← filteredUnfolds e
  let mut results := #[]
  let mut forbidden := HashSet.empty.insert s! "show {← printToPaste (← mkEq e e)} from rfl"
  for replacement in replacements do
    let rfl := s! "show {← printToPaste (← mkEq e replacement)} from rfl"
    unless forbidden.contains rfl do
      forbidden := forbidden.insert rfl
      results := results.push (replacement, mkRewrite occ false rfl loc)
  return results

def renderDefinitions (defs : Array (Expr × String)) (range : Lsp.Range)
    (doc : FileWorker.EditableDocument) : MetaM Html := do
  return <details «open»={true}>
    <summary className="mv2 pointer">
      {.text "Definitional rewrites:"}
    </summary>
    {
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
      ← defs.mapM fun (replacement, tactic) => do
        return <li> {
          .element "p" #[] <|
            #[<span className="font-code" style={json% { "white-space" : "pre-wrap" }}> {
              Html.ofComponent MakeEditLink
                (.ofReplaceRange doc.meta range tactic)
                #[.text $ Format.pretty $ (← Meta.ppExpr replacement)] }
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

      let some (subExpr, occ) ← viewKAbstractSubExpr (← loc.rootExpr) loc.pos |
        return .text "rw doesn't work on expressions with bound variables."
      let results ← unfoldsWithTacticString subExpr occ (← loc.location)
      if results.isEmpty then
        return <span>
          could not find a definition for {<InteractiveCode fmt={← ppExprTagged subExpr}/>}
        </span>
      renderDefinitions results props.replaceRange doc


@[widget_module]
def InteractiveUnfold : Component SelectInsertParams :=
  mk_rpc_widget% InteractiveUnfold.rpc


/-- Unfold the selected expression any number of times.
After each unfold, we apply `whnfCore` to simplify the expression.
Explicit natural number expressions are copmuted directly.

To use `unfold?`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `unfold?` by a tactic that performs this rewrite.
-/
elab stx:"unfold?" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash InteractiveUnfold.javascript)
    (pure $ json% { replaceRange : $range }) stx
