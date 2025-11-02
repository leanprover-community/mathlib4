/-
Copyright (c) 2023 Robin Böhne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne, Wojciech Nawrocki, Patrick Massot
-/
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Data.String.Defs
import Batteries.Tactic.Lint

/-! # Conv widget

This is a slightly improved version of one of the examples in the ProofWidget library.
It defines a `conv?` tactic that displays a widget panel allowing to generate
a `conv` call zooming to the subexpression selected in the goal.
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
      if (← Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
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

    return { expr := nextExp, val? := toString count, listRest := pathRest }

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
      expr := ← (Lean.Core.viewSubexpr path.head! expr)
      val? := toString (path.head! + 1)
      listRest := path.tail!
    }

open Lean Syntax in
/-- Return the link text and inserted text above and below of the conv widget. -/
@[nolint unusedArguments]
def insertEnter (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (params : SelectInsertParams) :
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)) := do
  let some pos := locations[0]? | throwError "You must select something."
  let (fvar, subexprPos) ← match pos with
  | ⟨_, .target subexprPos⟩ => pure (none, subexprPos)
  | ⟨_, .hypType fvar subexprPos⟩ => pure (some fvar, subexprPos)
  | ⟨_, .hypValue fvar subexprPos⟩ => pure (some fvar, subexprPos)
  | _ => throwError "You must select something in the goal or in a local value."
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
  -- prepare `enter` indentation
  let spc := String.replicate (SelectInsertParamsClass.replaceRange params).start.character ' '
  let loc ← match fvar with
  | some fvarId => pure s!"at {← fvarId.getUserName} "
  | none => pure ""
  let mut enterval := s!"conv {loc}=>\n{spc}  enter {retList}"
  if enterval.contains '0' then enterval := "Error: Not a valid conv target"
  if retList.isEmpty then enterval := ""
  return ("Generate conv", enterval, none)

/-- Rpc function for the conv widget. -/
@[server_rpc_method]
def ConvSelectionPanel.rpc :=
mkSelectionPanelRPC insertEnter
  "Use shift-click to select one sub-expression in the goal that you want to zoom on."
  "Conv 🔍" (onlyGoal := false) (onlyOne := true)

/-- The conv widget. -/
@[widget_module]
def ConvSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% ConvSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal. -/
elab stx:"conv?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo ConvSelectionPanel.javascriptHash
    (pure <| json% { replaceRange: $(replaceRange) }) stx
