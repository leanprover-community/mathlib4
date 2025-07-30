/-
Copyright (c) 2023 Robin Böhne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne, Wojciech Nawrocki, Patrick Massot, Aaron Liu
-/
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Data.String.Defs
import Batteries.Tactic.Lint
import Batteries.Lean.Position

/-! # Conv widget

This is a slightly improved version of one of the examples in the ProofWidget library.
It defines a `conv?` tactic that displays a widget panel allowing to generate
a `conv` call zooming to the subexpression selected in the goal.
-/


open Lean Meta Server ProofWidgets

private inductive Path where
  | node : Path
  | arg (arg : Nat) (all : Bool) (next : Path) : Path
  | fun (depth : Nat) : Path
  | type (next : Path) : Path
  | body (name : Name) (next : Path) : Path

private partial def Path.ofSubExprPos (expr : Expr) (pos : SubExpr.Pos) : MetaM Path :=
  go expr pos.toArray 0
where
  go (expr : Expr) (pos : Array Nat) (i : Fin (pos.size + 1)) : MetaM Path :=
    if h : i = Fin.last pos.size then pure .node else
    let i := i.castLT (Fin.val_lt_last h)
    if pos[i] = SubExpr.Pos.typeCoord then
      throwError m!"conv mode does not support entering types{indentExpr expr}" else
    let err := throwError m!"cannot access position {pos[i]} of{indentExpr expr}"
    match expr with
    | .bvar i => throwError m!"unexpected bound variable #{i}"
    | .fvar _
    | .mvar _
    | .lit _
    | .const _ _
    | .sort _ => err
    | .proj _ _ e =>
      throwError m!"conv mode does not yet support entering projections{indentExpr expr}"
    | .mdata _ e => go e pos i.castSucc
    | .letE n t _ b _ =>
      if pos[i] = 0 then
        throwError m!"conv mode does not yet support entering let types{indentExpr expr}"
      else if pos[i] = 1 then
        throwError m!"conv mode does not yet support entering let values{indentExpr expr}"
      else if pos[i] = 2 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t
        withReader (fun ctx => {ctx with lctx}) do
          let e := b.instantiate1 (.fvar fvarId)
          unless (← isTypeCorrect e) do
            throwError m!"failed to abstract let-expression, \
              result is not type correct{indentExpr expr}"
          Path.body n <$> go e pos i.succ
      else err
    | .forallE n t b bi =>
      if pos[i] = 0 then do
        unless (← isProp t) || expr.isArrow do
          throwError m!"conv mode only supports rewriting forall binder types \
            when the binder type is a proposition{indentExpr expr}"
        Path.type <$> go t pos i.succ
      else if pos[i] = 1 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (Path.body n <$> go (b.instantiate1 (.fvar fvarId)) pos i.succ)
      else err
    | .lam n t b bi =>
      if pos[i] = 0 then
        throwError m!"conv mode does not support rewriting \
          the binder type of a lambda{indentExpr expr}"
      else if pos[i] = 1 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (Path.body n <$> go (b.instantiate1 (.fvar fvarId)) pos i.succ)
      else err
    | .app .. => appT expr pos i.castSucc [] none
  appT (e : Expr) (p : Array Nat) (i : Fin (p.size + 1))
      (acc : List Expr) (n : Option (Fin acc.length)) : MetaM Path :=
    match e with
    | .app f a =>
      if let some u := n then appT f p i (a :: acc) (some u.succ)
      else if h : i = Fin.last p.size then pure (Path.fun acc.length)
      else let i := i.castLT (Fin.val_lt_last h)
      if p[i] = 0 then appT f p i.succ (a :: acc) none
      else if p[i] = 1 then appT f p i.succ (a :: acc) (some ⟨0, acc.length.zero_lt_succ⟩)
      else throwError m!"cannot access position {p[i]} of{indentExpr e}"
    | _ =>
      if let some u := n then do
        let c ← PrettyPrinter.Delaborator.getParamKinds e acc.toArray
        if let some {bInfo := .default, ..} := c[u]? then
          arg (((c.map (·.bInfo)).take u).count .default + 1)
            false <$> go acc[u] p i
        else arg (u + 1) true <$> go acc[u] p i
      else arg 0 false <$> go e p i

private def getName (n : Name) : String :=
  match n with
  | Name.str _ s => s
  | _ => "_"

private def pathToString (path : Path) (spc : String) : String :=
  let c := go path
  let cc := List.replicate c.2 "fun"
  s!"\n{spc}  ".intercalate (if c.1 = [] then cc else s!"enter [{", ".intercalate c.1}]" :: cc)
where
  go : Path → List String × Nat
    | Path.node => ([], 0)
    | Path.arg arg all next =>
      (s!"{if all then "@" else ""}{arg}" :: (go next).1, (go next).2)
    | Path.fun depth => ([], depth)
    | Path.type next => ("1" :: (go next).1, (go next).2)
    | Path.body name next => (getName name.eraseMacroScopes :: (go next).1, (go next).2)

open Lean Syntax in
/-- Return the link text and inserted text above and below of the conv widget. -/
def insertEnter (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (params : SelectInsertParams) : MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let some pos := locations[0]? | throwError "You must select something."
  let (fvar, subexprPos) ← match pos with
  | ⟨_, .target subexprPos⟩ => pure (none, subexprPos)
  | ⟨_, .hypType fvar subexprPos⟩ => pure (some fvar, subexprPos)
  | _ => throwError "You must select something in the goal or in the type of a local hypothesis."
  let expr ← fvar.elim (pure goalType) fun fvarId => fvarId.getType
  let expr ← instantiateMVars expr
  -- generate list of commands for `enter`
  let path ← Path.ofSubExprPos expr subexprPos
  -- prepare `enter` indentation
  let spc := String.replicate (SelectInsertParamsClass.replaceRange params).start.character ' '
  -- build `enter [...]` string
  let enterString := pathToString path spc
  let loc ← match fvar with
  | some fvarId => pure s!"at {← fvarId.getUserName} "
  | none => pure ""
  let enterval := if enterString = "" then "" else s!"conv {loc}=>\n{spc}  {enterString}"
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
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo ConvSelectionPanel.javascriptHash
   (pure <| json% { replaceRange: $(replaceRange) }) stx
