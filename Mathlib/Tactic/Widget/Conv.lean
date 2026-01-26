/-
Copyright (c) 2023 Robin Böhne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Böhne, Wojciech Nawrocki, Patrick Massot, Aaron Liu
-/
module

public import Mathlib.Lean.Name
public import Mathlib.Tactic.Widget.SelectPanelUtils
public import ProofWidgets.Component.OfRpcMethod
public import Lean.Server.Rpc.RequestHandling
public import ProofWidgets.Component.Basic
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-! # Conv widget

This is a slightly improved version of one of the examples that used to be
in the ProofWidget library. It defines a `conv?` tactic that displays a widget panel
allowing to generate a `conv` call zooming to the subexpression selected in the goal.
-/

meta section

open Lean Meta

namespace Mathlib.Tactic.Conv

/--
A path to a subexpression from a root expression.
The constructors are chosen to be easily translatable into `conv` directions.
-/
inductive Path where
  /--
  Accesses the `arg`th implicit or explicit argument,
  depending on whether `all` is `true` or `false`, respectively.
  Corresponds to the `conv` tactic `arg`.
  For example, `Path.arg 3 true next` is `arg @3` followed by `next`,
  and `Path.arg 0 false next` is `arg 0` followed by `next`.
  -/
  | arg (arg : Nat) (all : Bool) (next : Path) : Path
  /--
  End a `conv` sequence with `depth`-many repetitions of the `conv` tactic `fun`.
  For example, `Path.fun 3` corresponds to the `conv` sequence `fun; fun; fun`,
  and `Path.fun 0` just terminates a `Path` without any extra `conv` tactics.
  -/
  | fun (depth : Nat) : Path
  /--
  Traverses into the binder type of a forall, let, or lambda.
  Currently out of these three options `conv` only supports going into
  the binder type of a forall, but in the future if `conv` gets support for
  going into let or lambda binding types with different `conv` tactics we may add
  additional arguments to specify whether the binder is a forall, let, or lambda.
  Corresponds to the `conv` tactics `lhs` or `arg`.
  -/
  | type (next : Path) : Path
  /--
  Traverses into the body of a forall, let, or lambda.
  Corresponds to the `conv` tactics `intro` or `ext`.
  -/
  | body (name : Name) (next : Path) : Path

/--
Given an `e : Expr` and `pos : SubExpr.Pos`, `Path.ofSubExprPosArray expr pos.toArray` generates
the `Path` corresponding to traversing `pos` starting at the reference expression `e`.
-/
partial def Path.ofSubExprPosArray (expr : Expr) (pos : Array Nat) : MetaM Path :=
  go expr 0
where
  /--
  `Path.ofSubExprPosArray.go pos expr i` is the same as `Path.ofSubExprPosArray expr (pos.drop i)`
  -/
  go (expr : Expr) (i : Fin (pos.size + 1)) : MetaM Path :=
    if h : i = Fin.last pos.size then pure (Path.fun 0) else
    let i := i.castLT (Fin.val_lt_last h)
    if pos[i] = SubExpr.Pos.typeCoord then
      throwError m!"conv mode does not support entering types of expressions{indentExpr expr}" else
    let err := m!"{.ofConstName ``SubExpr.Pos (fullNames := true)} position {pos[i]} \
      is invalid for{indentExpr expr}"
    match expr with
    | .bvar i => throwError m!"unexpected bound variable #{i}"
    | .fvar _
    | .mvar _
    | .lit _
    | .const _ _
    | .sort _ => throwError err
    | .proj _ _ e =>
      throwError m!"conv mode does not yet support entering projections{indentExpr expr}"
    | .mdata _ e => go e i.castSucc
    | .letE n t _ b _ =>
      if pos[i] = 0 then -- let binder type
        throwError m!"conv mode does not yet support entering let types{indentExpr expr}"
      else if pos[i] = 1 then -- let binder value
        throwError m!"conv mode does not yet support entering let values{indentExpr expr}"
      else if pos[i] = 2 then -- let body
        withLocalDeclNoLocalInstanceUpdate n .default t fun fvar => do
          let e := b.instantiate1 fvar
          unless (← isTypeCorrect e) do
            throwError m!"conv mode does not support entering let expressions \
              for which the type-correctness of the body depends on the let value \n\
              failed to abstract let-expression, result is not type correct{indentExpr expr}"
          Path.body n <$> go e i.succ
      else throwError err
    | .forallE n t b bi =>
      if pos[i] = 0 then do -- forall binder type
        unless (← isProp t) || expr.isArrow do
          throwError m!"conv mode only supports rewriting forall binder types \
            when the binder type is a proposition or when the body of the forall \
            does not depend on the value of the bound variable{indentExpr expr}"
        Path.type <$> go t i.succ
      else if pos[i] = 1 then -- forall body
        withLocalDeclNoLocalInstanceUpdate n bi t fun fvar =>
          (Path.body n <$> go (b.instantiate1 fvar) i.succ)
      else throwError err
    | .lam n t b bi =>
      if pos[i] = 0 then -- lambda binder type
        throwError m!"conv mode does not support rewriting \
          the binder type of a lambda{indentExpr expr}"
      else if pos[i] = 1 then -- lambda body
        withLocalDeclNoLocalInstanceUpdate n bi t fun fvar =>
          (Path.body n <$> go (b.instantiate1 fvar) i.succ)
      else throwError err
    | .app .. => appT expr i.castSucc [] none
  /-- Traverse an application from argument to function, accumulating arguments and consuming `pos`
  (incrementing `i`) as we approach the head. If `pos[i]` tells us to enter the argument of `.app`
  instead of the function at some point, we stop consuming `pos` and start counting arguments
  (`some n`) until we hit the head. This gives us enough information to determine the value for
  `Path.arg` once we reach the head, and then enter the argument we encountered earlier.

  Note: if we instead run out of `pos` before reaching the head, the `Path` is a chain of `fun`s.

  Note: `conv` does not see through `.mdata` surrounding an `.app`, so we do not here either. -/
  appT (expr : Expr) (i : Fin (pos.size + 1))
      (acc : List Expr) (n : Option (Fin acc.length)) : MetaM Path :=
    match expr with
    | .app f a =>
      if let some n := n then -- found the argument (it is `acc[n]`)
        appT f i (a :: acc) (some n.succ)
      else if h : i = Fin.last pos.size then pure (Path.fun acc.length) -- ran out of `pos`
      else
        let i := i.castLT (Fin.val_lt_last h)
        if pos[i] = 0 then -- app fun
          appT f i.succ (a :: acc) none
        else if pos[i] = 1 then -- app arg
          appT f i.succ (a :: acc) (some ⟨0, acc.length.zero_lt_succ⟩)
        else
          throwError m!"{.ofConstName ``SubExpr.Pos (fullNames := true)} position {pos[i]} \
            is invalid for{indentExpr expr}"
    | _ =>
      if let some n := n then do -- found the argument (it is `acc[n]`)
        let bis : Array BinderInfo :=
          (← PrettyPrinter.Delaborator.getParamKinds expr acc.toArray).map (·.bInfo)
        if bis[n]? == some .default then -- explicit argument
          -- find the number of explicit arguments between the head and this arg (inclusive)
          arg ((bis.take n).count .default + 1)
            false <$> go acc[n] i
        else arg (n + 1) true <$> go acc[n] i -- implicit argument
      else -- ran out of `Expr.app` nodes
        arg 0 false <$> go expr i

open Lean.Parser.Tactic.Conv in
/--
Given a `path : Path` and `xs : TSepArray ``enterArg ","`, generate the `conv` syntax
corresponding to `enter [xs,*]` followed by traversing `path`. If `loc` is `some fvar`,
start with `conv at fvar =>`, otherwise if `loc` is `none` start with `conv =>`.
We end every `conv` sequence with `skip`, and highlight `skip` upon insertion.
-/
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
    let seq ← `(convSeq1Indented| $arr:conv*)
    match loc with
    | none => `(tactic| conv => $seq:convSeq1Indented)
    | some n => `(tactic| conv at $(← mkIdentFromRef n):ident => $seq:convSeq1Indented)

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

/-- Return the text for the link in the conv widget that inserts the replacement,
and also return the replacement, and the range within the file to highlight after the
replacement is inserted. The highlighted range will always be the trailing `skip`. -/
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
public protected def SelectionPanel.rpc :=
  mkSelectionPanelRPC insertEnter
    "Use shift-click to select one sub-expression in the goal or local context that you want to \
    zoom in on."
    "Conv 🔍" (onlyGoal := false) (onlyOne := true)

/-- The conv widget. -/
@[widget_module]
public protected def SelectionPanel : ProofWidgets.Component SelectInsertParams :=
  mk_rpc_widget% SelectionPanel.rpc

/-- Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal or in the type of a local hypothesis or let-decl. -/
elab stx:"conv?" : tactic => do
  let some replaceRange := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo Conv.SelectionPanel.javascriptHash
    (pure <| json% { replaceRange: $(replaceRange) }) stx

end Mathlib.Tactic.Conv
