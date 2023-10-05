/-
Copyright (c) 2023 Robin Böhne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne, Wojciech Nawrocki, Patrick Massot
-/
import Std.Lean.Position
import Mathlib.Tactic.Widget.Util

/-! # Conv widget

This is a slightly improved version of one of the examples in the ProofWidget library.
 -/

open Lean Meta Server ProofWidgets

private structure SolveReturn where
  expr : Expr
  val? : Option String
  listRest : List Nat

private def solveLevel (expr : Expr) (path : List Nat) : MetaM SolveReturn := match expr with
  | Expr.app _ _ => do
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []

    -- we go through the application until we reach the end, counting how many explicit arguments
    -- it has and noting whether they are explicit or implicit
    while descExp.isApp do
      if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!

    -- we get the correct `enter` command by subtracting the number of `true`s in our list
    let mut mutablePath := path
    let mut length := count
    explicitList := List.reverse explicitList
    while !mutablePath.isEmpty && mutablePath.head! == 0 do
      if explicitList.head! == true then
        count := count - 1
      explicitList := explicitList.tail!
      mutablePath := mutablePath.tail!

    let mut nextExp := expr
    while length > count do
      nextExp := nextExp.appFn!
      length := length - 1
    nextExp := nextExp.appArg!

    let pathRest := if mutablePath.isEmpty then [] else mutablePath.tail!

    return { expr := nextExp, val? := toString count , listRest := pathRest }

  | Expr.lam n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }

  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }

  | Expr.mdata _ b => do
    match b with
      | Expr.mdata _ _ => return { expr := b, val? := none, listRest := path }
      | _ => return { expr := b.appFn!.appArg!, val? := none, listRest := path.tail!.tail! }

  | _ => do
    return {
      expr := ←(Lean.Core.viewSubexpr path.head! expr)
      val? := toString (path.head! + 1)
      listRest := path.tail!
    }

open Lean Syntax in
def insertEnter (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
  (_ : SelectInsertParams): MetaM (String × String) := do
  let some pos := locations[0]? | throwError "You must select something."
  let ⟨_, .target subexprPos⟩ := pos | throwError "You must select something in the goal."
  let mut list := (SubExpr.Pos.toArray subexprPos).toList
    let mut expr := goalType
  let mut retList := []
  -- generate list of commands for `enter`
  while !list.isEmpty do
    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val::retList
    list := res.listRest

  -- build `enter [...]` string
  retList := List.reverse retList
  let mut enterval := "conv => enter " ++ toString retList
  if enterval.contains '0' then enterval := "Error: Not a valid conv target"
  if retList.isEmpty then enterval := ""
  return ("Generate conv", enterval)


@[server_rpc_method]
def ConvSelectionPanel.rpc :=
mkSelectionPanelRPC insertEnter "Use shift-click to select one sub-expression in the goal that you want to zoom on." "Conv 🔍"


@[widget_module]
def ConvSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% ConvSelectionPanel.rpc

open scoped Json in
elab stx:"conv?" : tactic => do
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  savePanelWidgetInfo stx ``ConvSelectionPanel $ pure $ json% { replaceRange: $(replaceRange) }
