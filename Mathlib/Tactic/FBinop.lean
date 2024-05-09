/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.ToExpr

/-! # Elaborator for functorial binary operators

`fbinop% f x y` elaborates `f x y` for `x : S α` and `y : S' β`, taking into account
any coercions that the "functors" `S` and `S'` possess.

While `binop%` tries to solve for a single minimal type, `fbinop%` tries to solve
the parameterized problem of solving for a single minimal "functor."

The code is drawn from the Lean 4 core `binop%` elaborator. Two simplifications made were
1. It is assumed that every `f` has a "homogeneous" instance
   (think `Set.prod : Set α → Set β → Set (α × β)`).
2. It is assumed that there are no "non-homogeneous" default instances.

It also makes the assumption that the binop wants to be as homogeneous as possible.
For example, when the type of an argument is unknown it will try to unify the argument's type
with `S _`, which can help certain elaboration problems proceed (like for `{a,b,c}` notation).

The main goal is to support generic set product notation and have it elaborate in a convenient way.
-/

namespace FBinopElab
open Lean Elab Term Meta

initialize registerTraceClass `Elab.fbinop

/-- `fbinop% f x y` elaborates `f x y` for `x : S α` and `y : S' β`, taking into account
any coercions that the "functors" `S` and `S'` possess. -/
syntax:max (name := prodSyntax) "fbinop% " ident ppSpace term:max ppSpace term:max : term

/-- Tree recording the structure of the `fbinop%` expression. -/
private inductive Tree where
  /-- Leaf of the tree. Stores the generated `InfoTree` from elaborating `val`. -/
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  /-- An `fbinop%` node.
  `ref` is the original syntax that expanded into `binop%`.
  `f` is the constant for the binary operator -/
  | binop (ref : Syntax) (f : Expr) (lhs rhs : Tree)
  /-- Store macro expansion information to make sure that "go to definition" behaves
  similarly to notation defined without using `fbinop%`. -/
  | macroExpansion (macroName : Name) (stx stx' : Syntax) (nested : Tree)

private partial def toTree (s : Syntax) : TermElabM Tree := do
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result
where
  go (s : Syntax) : TermElabM Tree := do
    match s with
    | `(fbinop% $f $lhs $rhs) => processBinOp s f lhs rhs
    | `(($e)) =>
      if hasCDot e then
        processLeaf s
      else
        go e
    | _ =>
      withRef s do
        match ← liftMacroM <| expandMacroImpl? (← getEnv) s with
        | some (macroName, s?) =>
          let s' ← liftMacroM <| liftExcept s?
          withPushMacroExpansionStack s s' do
            return .macroExpansion macroName s s' (← go s')
        | none => processLeaf s

  processBinOp (ref : Syntax) (f lhs rhs : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstant f.getId
    return .binop ref f (← go lhs) (← go rhs)

  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e

/-- Records a "functor", which is some function `Type u → Type v`. We only
allow `c a1 ... an` for `c` a constant. This is so we can abstract out the universe variables. -/
structure SRec where
  name : Name
  args : Array Expr
  deriving Inhabited, ToExpr

/-- Given a type expression, try to remove the last argument(s) and create an `SRec` for the
underlying "functor". Only applies to function applications with a constant head, and,
after dropping all instance arguments, it requires that the remaining last argument be a type.
Returns the `SRec` and the argument. -/
private partial def extractS (e : Expr) : TermElabM (Option (SRec × Expr)) :=
  match e with
  | .letE .. => extractS (e.letBody!.instantiate1 e.letValue!)
  | .mdata _ b => extractS b
  | .app .. => do
    let f := e.getAppFn
    let .const n _ := f | return none
    let mut args := e.getAppArgs
    let mut info := (← getFunInfoNArgs f args.size).paramInfo
    for _ in [0 : args.size - 1] do
      if info.back.isInstImplicit then
        args := args.pop
        info := info.pop
      else
        break
    let x := args.back
    unless ← Meta.isType x do return none
    return some ({name := n, args := args.pop}, x)
  | _ => return none

/-- Computes `S x := c a1 ... an x` if it is type correct.
Inserts instance arguments after `x`. -/
private def applyS (S : SRec) (x : Expr) : TermElabM (Option Expr) :=
  try
    let f ← mkConstWithFreshMVarLevels S.name
    let v ← elabAppArgs f #[] ((S.args.push x).map .expr)
      (expectedType? := none) (explicit := true) (ellipsis := false)
    -- Now elaborate any remaining instance arguments
    elabAppArgs v #[] #[] (expectedType? := none) (explicit := false) (ellipsis := false)
  catch _ =>
    return none

/-- For a given argument `x`, checks if there is a coercion from `fromS x` to `toS x`
if these expressions are type correct. -/
private def hasCoeS (fromS toS : SRec) (x : Expr) : TermElabM Bool := do
  let some fromType ← applyS fromS x | return false
  let some toType ← applyS toS x | return false
  trace[Elab.fbinop] m!"fromType = {fromType}, toType = {toType}"
  withLocalDeclD `v fromType fun v => do
    match ← coerceSimple? v toType with
    | .some _ => return true
    | .none   => return false
    | .undef  => return false -- TODO: should we do something smarter here?

/-- Result returned by `analyze`. -/
private structure AnalyzeResult where
  maxS? : Option SRec := none
  /-- `true` if there are two types `α` and `β` where we don't have coercions in any direction. -/
  hasUncomparable : Bool := false

/-- Compute a minimal `SRec` for an expression tree. -/
private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let maxS? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType ← instantiateMVars expectedType
      if let some (S, _) ← extractS expectedType then
        pure S
      else
        pure none
  (go t *> get).run' { maxS? }
where
  go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
    unless (← get).hasUncomparable do
      match t with
      | .macroExpansion _ _ _ nested => go nested
      | .binop _ _ lhs rhs => go lhs; go rhs
      | .term _ _ val =>
        let type ← instantiateMVars (← inferType val)
        let some (S, x) ← extractS type
          | return -- Rather than marking as incomparable, let's hope there's a coercion!
        match (← get).maxS? with
        | none     => modify fun s => { s with maxS? := S }
        | some maxS =>
          let some maxSx ← applyS maxS x | return -- Same here.
          unless ← withNewMCtxDepth <| isDefEqGuarded maxSx type do
            if ← hasCoeS S maxS x then
              return ()
            else if ← hasCoeS maxS S x then
              modify fun s => { s with maxS? := S }
            else
              trace[Elab.fbinop] "uncomparable types: {maxSx}, {type}"
              modify fun s => { s with hasUncomparable := true }

private def mkBinOp (f : Expr) (lhs rhs : Expr) : TermElabM Expr := do
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] (expectedType? := none)
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/-- Turn a tree back into an expression. -/
private def toExprCore (t : Tree) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref f lhs rhs =>
    withRef ref <| withInfoContext' ref (mkInfo := mkTermInfo .anonymous ref) do
      let lhs ← toExprCore lhs
      let mut rhs ← toExprCore rhs
      mkBinOp f lhs rhs
  | .macroExpansion macroName stx stx' nested =>
    withRef stx <| withInfoContext' stx (mkInfo := mkTermInfo macroName stx) do
      withMacroExpansion stx stx' do
        toExprCore nested

/-- Try to coerce elements in the tree to `maxS` when needed. -/
private def applyCoe (t : Tree) (maxS : SRec) : TermElabM Tree := do
  go t none
where
  go (t : Tree) (f? : Option Expr) : TermElabM Tree := do
    match t with
    | .binop ref f lhs rhs =>
      let lhs' ← go lhs f
      let rhs' ← go rhs f
      return .binop ref f lhs' rhs'
    | .term ref trees e =>
      let type ← instantiateMVars (← inferType e)
      trace[Elab.fbinop] "visiting {e} : {type}"
      let some (_, x) ← extractS type
        | -- We want our operators to be "homogenous" so do a defeq check as an elaboration hint
          let x' ← mkFreshExprMVar none
          let some maxType ← applyS maxS x' | trace[Elab.fbinop] "mvar apply failed"; return t
          trace[Elab.fbinop] "defeq hint {maxType} =?= {type}"
          _ ← isDefEqGuarded maxType type
          return t
      let some maxType ← applyS maxS x
        | trace[Elab.fbinop] "applying {Lean.toExpr maxS} {x} failed"
          return t
      trace[Elab.fbinop] "{type} =?= {maxType}"
      if ← isDefEqGuarded maxType type then
        return t
      else
        trace[Elab.fbinop] "added coercion: {e} : {type} => {maxType}"
        withRef ref <| return .term ref trees (← mkCoe maxType e)
    | .macroExpansion macroName stx stx' nested =>
      withRef stx <| withPushMacroExpansionStack stx stx' do
        return .macroExpansion macroName stx stx' (← go nested f?)

private def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
  let r ← analyze tree expectedType?
  trace[Elab.fbinop] "hasUncomparable: {r.hasUncomparable}, maxType: {Lean.toExpr r.maxS?}"
  if r.hasUncomparable || r.maxS?.isNone then
    let result ← toExprCore tree
    ensureHasType expectedType? result
  else
    let result ← toExprCore (← applyCoe tree r.maxS?.get!)
    trace[Elab.fbinop] "result: {result}"
    ensureHasType expectedType? result

@[term_elab prodSyntax]
def elabBinOp : TermElab := fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

end FBinopElab
