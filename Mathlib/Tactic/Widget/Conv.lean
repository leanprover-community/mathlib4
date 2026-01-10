/-
Copyright (c) 2023 Robin Böhne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne, Wojciech Nawrocki, Patrick Massot, Aaron Liu
-/
module

public meta import Mathlib.Data.String.Defs
public meta import Mathlib.Lean.Name
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Lean.Server.Rpc.RequestHandling
public import Mathlib.Tactic.Widget.SelectPanelUtils
public import ProofWidgets.Component.Basic
public import ProofWidgets.Component.OfRpcMethod

/-! # Conv widget

This is a slightly improved version of one of the examples that used to be
in the ProofWidget library. It defines a `conv?` tactic that displays a widget panel
allowing to generate a `conv` call zooming to the subexpression selected in the goal.
-/

meta section

open Lean Meta Server ProofWidgets

inductive Path where
  | arg (arg : Nat) (all : Bool) (next : Path) : Path
  | fun (depth : Nat) : Path
  | type (next : Path) : Path
  | body (name : Name) (next : Path) : Path

partial def Path.ofSubExprPosArray (expr : Expr) (pos : Array Nat) : MetaM Path :=
  go expr 0
where
  go (expr : Expr) (i : Fin (pos.size + 1)) : MetaM Path :=
    if h : i = Fin.last pos.size then pure (Path.fun 0) else
    let i := i.castLT (Fin.val_lt_last h)
    if pos[i] = SubExpr.Pos.typeCoord then
      throwError m!"conv mode does not support entering types of expressions{indentExpr expr}" else
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
    | .mdata _ e => go e i.castSucc
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
            throwError m!"conv mode does not support entering let expressions \
              for which the type-correctness of the body depends on the let value \n\
              failed to abstract let-expression, result is not type correct{indentExpr expr}"
          Path.body n <$> go e i.succ
      else err
    | .forallE n t b bi =>
      if pos[i] = 0 then do
        unless (← isProp t) || expr.isArrow do
          throwError m!"conv mode only supports rewriting forall binder types \
            when the binder type is a proposition or when the body of the forall \
            does not depend on the value of the bound variable{indentExpr expr}"
        Path.type <$> go t i.succ
      else if pos[i] = 1 then do
        let lctx ← getLCtx
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t bi
        withReader (fun ctx => {ctx with lctx})
          (Path.body n <$> go (b.instantiate1 (.fvar fvarId)) i.succ)
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
          (Path.body n <$> go (b.instantiate1 (.fvar fvarId)) i.succ)
      else err
    | .app .. => appT expr i.castSucc [] none
  appT (e : Expr) (i : Fin (pos.size + 1))
      (acc : List Expr) (n : Option (Fin acc.length)) : MetaM Path :=
    match e with
    | .app f a =>
      if let some u := n then appT f i (a :: acc) (some u.succ)
      else if h : i = Fin.last pos.size then pure (Path.fun acc.length)
      else let i := i.castLT (Fin.val_lt_last h)
      if pos[i] = 0 then appT f i.succ (a :: acc) none
      else if pos[i] = 1 then appT f i.succ (a :: acc) (some ⟨0, acc.length.zero_lt_succ⟩)
      else throwError m!"cannot access position {pos[i]} of{indentExpr e}"
    | _ =>
      if let some u := n then do
        let c ← PrettyPrinter.Delaborator.getParamKinds e acc.toArray
        if let some {bInfo := .default, ..} := c[u]? then
          arg (((c.map (·.bInfo)).take u).count .default + 1)
            false <$> go acc[u] i
        else arg (u + 1) true <$> go acc[u] i
      else arg 0 false <$> go e i

open Lean.Parser.Tactic.Conv in
def pathToStx {m} [Monad m] [MonadEnv m] [MonadRef m] [MonadQuotation m]
    (path : Path) (loc : Option Name) (xs : Syntax.TSepArray ``enterArg "," := {}) :
    m (TSyntax `tactic) := do
  match path with
  | Path.arg arg all next =>
    let num := Syntax.mkNumLit (toString arg) (← MonadRef.mkInfoFromRefPos)
    let arg ← if all then `(enterArg| @$num:num)
      else `(enterArg| $num:num)
    pathToStx next loc (xs.push arg)
  | Path.type next =>
    let arg ← `(enterArg| 1)
    pathToStx next loc (xs.push arg)
  | Path.body name next =>
    let bi ←
      if name.eraseMacroScopes.willRoundTrip then
        `(binderIdent| $(← mkIdentFromRef name.eraseMacroScopes):ident)
      else `(binderIdent| _)
    let arg ← `(enterArg| $bi:binderIdent)
    pathToStx next loc (xs.push arg)
  | Path.fun depth =>
    let capacity := if xs.elemsAndSeps.isEmpty
      then depth + 1 -- `fun`*depth; `skip`
      else depth + 2 -- `conv [args+]`; `fun`*depth; `skip`
    let mut arr := Array.emptyWithCapacity capacity
    let enterStx ← `(conv| enter [$xs,*])
    let funStx ← `(conv| fun)
    let skipStx ← `(conv| skip)
    if !xs.elemsAndSeps.isEmpty then arr := arr.push enterStx
    for _ in [0:depth] do arr := arr.push funStx
    arr := arr.push skipStx
    let seq ← `(convSeq1Indented|$arr:conv*)
    match loc with
    | none => `(tactic| conv => $seq:convSeq1Indented)
    | some n => `(tactic| conv at $(← mkIdentFromRef n):ident => $seq:convSeq1Indented)

open Lean Syntax in
/-- Return the syntax to insert for the conv widget.
Factored out of `insertEnter` for easy testing. -/
public def insertEnterSyntax (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) :
    MetaM Syntax := do
  let some pos := locations[0]? | throwError "You must select something."
  let (expr, subexprPos, fvarUserName?) ← match pos with
  | ⟨_, .target subexprPos⟩ => pure (goalType, subexprPos, none)
  | ⟨_, .hypType fvarId subexprPos⟩ => do
    let expr ← fvarId.getType
    let userName ← fvarId.getUserName
    pure (expr, subexprPos, some userName)
  | _ => throwError "You must select something in the goal or in the type of a local hypothesis."
  let expr ← instantiateMVars expr
  -- generate list of commands for `enter`
  let path ← Path.ofSubExprPosArray expr subexprPos.toArray
  pathToStx path fvarUserName?

open Lean Syntax in
/-- Return the text for the link in the conv widget that inserts the replacement,
and also return the replacement, and the range within the file to highlight after the
replacement is inserted. -/
public def insertEnter (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (params : SelectInsertParams) :
    MetaM (String × String × Option (String.Pos.Raw × String.Pos.Raw)) := do
  /-
  TODO: figure out a better way to determine indentation here
  The current method assumes the indentation level is the same as the column position of
  the `c` in the `conv?` syntax
  This is of course not always true, and so `conv?` will produce weirdly indented syntax sometimes
  For example,
  ```
  example : True := by conv?
  ```
  turns into
  ```
  example : True := by conv =>
                         skip
  ```
  Fortunately, the `conv` indentation is extremely permissive
  (relative indentation can be positive negative or zero),
  so this will probably never create non-working `conv` code.
  -/
  -- prepare indentation
  let column := (SelectInsertParamsClass.replaceRange params).start.character
  -- build `conv` syntax
  let enterStx ← insertEnterSyntax locations goalType
  let enterFormat ← PrettyPrinter.ppCategory `tactic enterStx
  let enterString := enterFormat.pretty (width := 100) (indent := column) (column := column)
  -- highlight trailing `skip` after insertion
  let trailingSkipRange? : Option (String.Pos.Raw × String.Pos.Raw) :=
    let trimmed := enterString.trimAsciiEnd
    trimmed.dropSuffix? "skip" |>.map (·.rawEndPos, trimmed.rawEndPos)
  return ("Generate conv", enterString, trailingSkipRange?)

/-- Rpc function for the conv widget. -/
@[server_rpc_method]
public def ConvSelectionPanel.rpc :=
  mkSelectionPanelRPC insertEnter
    "Use shift-click to select one sub-expression in the goal or local context that you want to \
    zoom in on."
    "Conv 🔍" (onlyGoal := false) (onlyOne := true)

/-- The conv widget. -/
@[widget_module]
public def ConvSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% ConvSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal or in the type of a local hypothesis or let-decl. -/
elab stx:"conv?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo ConvSelectionPanel.javascriptHash
    (pure <| json% { replaceRange: $(replaceRange) }) stx
