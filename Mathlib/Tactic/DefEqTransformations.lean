/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.Basic

/-! # Tactics that transform types into definitionally equal types

This module defines a standard wrapper that can be used to create tactics that
change hypotheses and the goal to things that are definitionally equal.

It then provides a number of tactics that transform local hypotheses and/or the target.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Elab.Tactic

/--
This is `Lean.MVarId.changeLocalDecl` but makes sure to preserve local variable order.
-/
def _root_.Lean.MVarId.changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let lctx := (← mvarId.getDecl).lctx
  let some decl := lctx.find? fvarId | throwTacticEx `changeLocalDecl mvarId m!"\
    local variable {Expr.fvar fvarId} is not present in local context{mvarId}"
  let toRevert := lctx.foldl (init := #[]) fun arr decl' =>
    if decl.index ≤ decl'.index then arr.push decl'.fvarId else arr
  let (_, mvarId) ← mvarId.withReverted toRevert fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

/-- For the main goal, use `m` to transform the types of locations specified by `loc?`.
If `loc?` is none, then transforms the type of target. `m` is provided with an expression
with instantiated metavariables as well as, if the location is a local hypothesis, the fvar.

`m` *must* transform expressions to defeq expressions.
If `checkDefEq = true` (the default) then `runDefEqTactic` will throw an error
if the resulting expression is not definitionally equal to the original expression. -/
def runDefEqTactic (m : Option FVarId → Expr → MetaM Expr)
    (loc? : Option (TSyntax ``Parser.Tactic.location))
    (tacticName : String)
    (checkDefEq : Bool := true) :
    TacticM Unit := withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← h.getType
      let ty' ← m h (← instantiateMVars ty)
      if Expr.equal ty ty' then
        return mvarId
      else
        mvarId.changeLocalDecl' (checkDefEq := checkDefEq) h ty')
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (checkDefEq := checkDefEq) (← m none ty))
    (failed := fun _ => throwError "{tacticName} failed")

/-- Like `Mathlib.Tactic.runDefEqTactic` but for `conv` mode. -/
def runDefEqConvTactic (m : Expr → MetaM Expr) : TacticM Unit := withMainContext do
  Conv.changeLhs <| ← m (← instantiateMVars <| ← Conv.getLhs)


/-! ### `whnf` -/

/--
`whnf at loc` puts the given location into weak-head normal form.
This also exists as a `conv`-mode tactic.

Weak-head normal form is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.
-/
elab "whnf" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ => whnf) loc? "whnf"


/-! ### `beta_reduce` -/

/--
`beta_reduce at loc` completely beta reduces the given location.
This also exists as a `conv`-mode tactic.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.
-/
elab (name := betaReduceStx) "beta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (checkDefEq := false) (fun _ e => Core.betaReduce e) loc? "beta_reduce"

@[inherit_doc betaReduceStx]
elab "beta_reduce" : conv => runDefEqConvTactic (Core.betaReduce ·)


/-! ### `reduce` -/

/--
`reduce at loc` completely reduces the given location.
This also exists as a `conv`-mode tactic.

This does the same transformation as the `#reduce` command.
-/
elab "reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ e => reduce e (skipTypes := false) (skipProofs := false)) loc? "reduce"


/-! ### `unfold_let` -/

/-- Unfold all the fvars from `fvars` in `e` that have local definitions (are "let-bound"). -/
def unfoldFVars (fvars : Array FVarId) (e : Expr) : MetaM Expr := do
  transform (usedLetOnly := true) e fun node => do
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        if let some val ← fvarId.getValue? then
          return .visit (← instantiateMVars val)
        else
          return .continue
      else
        return .continue
    | _ => return .continue

/--
`unfold_let x y z at loc` unfolds the local definitions `x`, `y`, and `z` at the given
location, which is known as "zeta reduction."
This also exists as a `conv`-mode tactic.

If no local definitions are given, then all local definitions are unfolded.
This variant also exists as the `conv`-mode tactic `zeta`.

This is similar to the `unfold` tactic, which instead is for unfolding global definitions.
-/
syntax (name := unfoldLetStx) "unfold_let" (ppSpace colGt term:max)*
  (ppSpace Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| unfold_let $[$loc?]?) =>
    runDefEqTactic (fun _ => zetaReduce) loc? "unfold_let"
  | `(tactic| unfold_let $hs:term* $[$loc?]?) => do
    let fvars ← getFVarIds hs
    runDefEqTactic (fun _ => unfoldFVars fvars) loc? "unfold_let"

@[inherit_doc unfoldLetStx]
syntax "unfold_let" (ppSpace colGt term:max)* : conv

elab_rules : conv
  | `(conv| unfold_let) => runDefEqConvTactic zetaReduce
  | `(conv| unfold_let $hs:term*) => do
    runDefEqConvTactic (unfoldFVars (← getFVarIds hs))


/-! ### `refold_let` -/

/-- For each fvar, looks for its body in `e` and replaces it with the fvar. -/
def refoldFVars (fvars : Array FVarId) (loc? : Option FVarId) (e : Expr) : MetaM Expr := do
  -- Filter the fvars, only taking those that are from earlier in the local context.
  let fvars ←
    if let some loc := loc? then
      let locIndex := (← loc.getDecl).index
      fvars.filterM fun fvar => do
        let some decl ← fvar.findDecl? | return false
        return decl.index < locIndex
    else
      pure fvars
  let mut e := e
  for fvar in fvars do
    let some val ← fvar.getValue?
      | throwError "local variable {Expr.fvar fvar} has no value to refold"
    e := (← kabstract e val).instantiate1 (Expr.fvar fvar)
  return e

/--
`refold_let x y z at loc` looks for the bodies of local definitions `x`, `y`, and `z` at the given
location and replaces them with `x`, `y`, or `z`. This is the inverse of "zeta reduction."
This also exists as a `conv`-mode tactic.
-/
syntax (name := refoldLetStx) "refold_let" (ppSpace colGt term:max)*
  (ppSpace Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| refold_let $hs:term* $[$loc?]?) => do
    let fvars ← getFVarIds hs
    runDefEqTactic (refoldFVars fvars) loc? "refold_let"

@[inherit_doc refoldLetStx]
syntax "refold_let" (ppSpace colGt term:max)* : conv

elab_rules : conv
  | `(conv| refold_let $hs:term*) => do
    runDefEqConvTactic (refoldFVars (← getFVarIds hs) none)


/-! ### `unfold_projs` -/

/-- Recursively unfold all the projection applications for class instances. -/
def unfoldProjs (e : Expr) : MetaM Expr := do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue

/--
`unfold_projs at loc` unfolds projections of class instances at the given location.
This also exists as a `conv`-mode tactic.
-/
elab (name := unfoldProjsStx) "unfold_projs" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => unfoldProjs) loc? "unfold_projs"

@[inherit_doc unfoldProjsStx]
elab "unfold_projs" : conv => runDefEqConvTactic unfoldProjs


/-! ### `eta_reduce` -/

/-- Eta reduce everything -/
def etaReduceAll (e : Expr) : MetaM Expr := do
  transform e fun node =>
    match node.etaExpandedStrict? with
    | some e' => return .visit e'
    | none => return .continue

/--
`eta_reduce at loc` eta reduces all sub-expressions at the given location.
This also exists as a `conv`-mode tactic.

For example, `fun x y => f x y` becomes `f` after eta reduction.
-/
elab (name := etaReduceStx) "eta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaReduceAll) loc? "eta_reduce"

@[inherit_doc etaReduceStx]
elab "eta_reduce" : conv => runDefEqConvTactic etaReduceAll


/-! ### `eta_expand` -/

/-- Eta expand every sub-expression in the given expression.

As a side-effect, beta reduces any pre-existing instances of eta expanded terms.  -/
partial def etaExpandAll (e : Expr) : MetaM Expr := do
  let betaOrApp (f : Expr) (args : Array Expr) : Expr :=
    if f.etaExpanded?.isSome then f.beta args else mkAppN f args
  let expand (e : Expr) : MetaM Expr := do
    if e.isLambda then
      return e
    else
      forallTelescopeReducing (← inferType e) fun xs _ => do
        mkLambdaFVars xs (betaOrApp e xs)
  transform e
    (pre := fun node => do
      if node.isApp then
        let f ← etaExpandAll node.getAppFn
        let args ← node.getAppArgs.mapM etaExpandAll
        .done <$> expand (betaOrApp f args)
      else
        pure .continue)
    (post := (.done <$> expand ·))

/--
`eta_expand at loc` eta expands all sub-expressions at the given location.
It also beta reduces any applications of eta expanded terms, so it puts it
into an eta-expanded "normal form."
This also exists as a `conv`-mode tactic.

For example, if `f` takes two arguments, then `f` becomes `fun x y => f x y`
and `f x` becomes `fun y => f x y`.

This can be useful to turn, for example, a raw `HAdd.hAdd` into `fun x y => x + y`.
-/
elab (name := etaExpandStx) "eta_expand" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaExpandAll) loc? "eta_expand"

@[inherit_doc etaExpandStx]
elab "eta_expand" : conv => runDefEqConvTactic etaExpandAll


/-! ### `eta_struct` -/

/-- Given an expression that's either a native projection or a registered projection
function, gives (1) the name of the structure type, (2) the index of the projection, and
(3) the object being projected. -/
def getProjectedExpr (e : Expr) : MetaM (Option (Name × Nat × Expr)) := do
  if let .proj S i x := e then
    return (S, i, x)
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if e.getAppNumArgs == info.numParams + 1 then
        if let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? info.ctorName then
          return (fVal.induct, info.i, e.appArg!)
  return none

/-- Checks if the expression is of the form `S.mk x.1 ... x.n` with `n` nonzero
and `S.mk` a structure constructor and returns `x`.
Each projection `x.i` can be either a native projection or from a projection function.

`tryWhnfR` controls whether to try applying `whnfR` to arguments when none of them
are obviously projections.

Once an obviously correct projection is found, relies on the structure eta rule in `isDefEq`. -/
def etaStruct? (e : Expr) (tryWhnfR : Bool := true) : MetaM (Option Expr) := do
  let .const f _ := e.getAppFn | return none
  let some (ConstantInfo.ctorInfo fVal) := (← getEnv).find? f | return none
  unless 0 < fVal.numFields && e.getAppNumArgs == fVal.numParams + fVal.numFields do return none
  unless isStructureLike (← getEnv) fVal.induct do return none
  let args := e.getAppArgs
  let mut x? ← findProj fVal args pure
  if tryWhnfR then
    if let .undef := x? then
      x? ← findProj fVal args whnfR
  if let .some x := x? then
    -- Rely on eta for structures to make the check:
    if ← isDefEq x e then
      return x
  return none
where
  /-- Check to see if there's an argument at some index `i`
  such that it's the `i`th projection of a some expression.
  Returns the expression. -/
  findProj (fVal : ConstructorVal) (args : Array Expr) (m : Expr → MetaM Expr) :
      MetaM (LOption Expr) := do
    for i in [0 : fVal.numFields] do
      let arg ← m args[fVal.numParams + i]!
      let some (S, j, x) ← getProjectedExpr arg | continue
      if S == fVal.induct && i == j then
        return .some x
      else
        -- Then the eta rule can't apply since there's an obviously wrong projection
        return .none
    return .undef

/-- Finds all occurrences of expressions of the form `S.mk x.1 ... x.n` where `S.mk`
is a structure constructor and replaces them by `x`. -/
def etaStructAll (e : Expr) : MetaM Expr :=
  transform e fun node => do
    if let some node' ← etaStruct? node then
      return .visit node'
    else
      return .continue

/--
`eta_struct at loc` transforms structure constructor applications such as `S.mk x.1 ... x.n`
(pretty printed as, for example, `{a := x.a, b := x.b, ...}`) into `x`.
This also exists as a `conv`-mode tactic.

The transformation is known as eta reduction for structures, and it yields definitionally
equal expressions.

For example, given `x : α × β`, then `(x.1, x.2)` becomes `x` after this transformation.
-/
elab (name := etaStructStx) "eta_struct" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ => etaStructAll) loc? "eta_struct"

@[inherit_doc etaStructStx]
elab "eta_struct" : conv => runDefEqConvTactic etaStructAll

end Mathlib.Tactic
