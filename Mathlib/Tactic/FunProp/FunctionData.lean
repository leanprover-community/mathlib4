/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module


public meta import Mathlib.Tactic.FunProp.Mor
public import Mathlib.Tactic.FunProp.Mor
public import Mathlib.Tactic.FunProp.ToBatteries
public meta import Std.Do

/-!
## `funProp` data structure holding information about a function

`FunctionData` holds data about function in the form `fun x ↦ f x₁ ... xₙ`.
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/-- Structure storing parts of a function in funProp-normal form. -/
structure FunctionData where
  /-- local context where `mainVar` exists -/
  lctx : LocalContext
  /-- local instances -/
  insts : LocalInstances
  /-- main function -/
  fn : Expr
  /-- applied function arguments -/
  args : Array Mor.Arg
  /-- main variable -/
  mainVar : Expr
  /-- indices of `args` that contain `mainVars` -/
  mainArgs : Array Nat

/-- Turn function data back to expression. -/
def FunctionData.toExpr (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

/-- Is `f` an identity function? -/
def FunctionData.isIdentityFun (f : FunctionData) : Bool :=
  (f.args.size = 0 && f.fn == f.mainVar)

/-- Is `f` a constant function? -/
def FunctionData.isConstantFun (f : FunctionData) : Bool :=
  ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

/-- Domain type of `f`. -/
def FunctionData.domainType (f : FunctionData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    inferType f.mainVar

/-- Is head function of `f` a constant?

If the head of `f` is a projection return the name of corresponding projection function. -/
def FunctionData.getFnConstName? (f : FunctionData) : MetaM (Option Name) := do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let some info := getStructureInfo? (← getEnv) typeName | return none
    let some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none


/-- Get `FunctionData` for `f`. Throws if `f` can't be put into funProp-normal form. -/
def getFunctionData (f : Expr) : MetaM FunctionData := do
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mut fn := fn
      let mut args := args

      -- revert projection in fn
      if let .proj n i x := fn then
        let some info := getStructureInfo? (← getEnv) n | unreachable!
        let some projName := info.getProjFn? i | unreachable!
        let p ← mkAppM projName #[x]
        fn := p.getAppFn
        args := p.getAppArgs.map (fun a => {expr:=a}) ++ args

      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i else none)
        |>.filterMap id

      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }

/-- Result of `getFunctionData?`. It returns function data if the function is in the form
`fun x ↦ f y₁ ... yₙ`. Two other cases are `fun x ↦ let y := ...` or `fun x y ↦ ...` -/
inductive MaybeFunctionData where
  /-- Can't generate function data as function body has let binder. -/
  | letE (f : Expr)
  /-- Can't generate function data as function body has lambda binder. -/
  | lam (f : Expr)
  /-- Function data has been successfully generated. -/
  | data (fData : FunctionData)

/-- Turn `MaybeFunctionData` to the function. -/
def MaybeFunctionData.get (fData : MaybeFunctionData) : MetaM Expr :=
  match fData with
  | .letE f | .lam f => pure f
  | .data d => d.toExpr

/-- Get `FunctionData` for `f`. -/
def getFunctionData? (f : Expr)
    (unfoldPred : Name → Bool := fun _ => false) :
    MetaM MaybeFunctionData := do
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do

  let unfold := fun e : Expr => do
    if let some n := e.getAppFn'.constName? then
      pure ((unfoldPred n) || (← isReducible n))
    else
      pure false

  let .forallE xName xType _ _ ← instantiateMVars (← inferType f)
    | throwError m!"fun_prop bug: function expected, got `{f} : {← inferType f}, \
                    type ctor {(← inferType f).ctorName}"
  withLocalDeclD xName xType fun x => do
    let fx' := (← Mor.whnfPred (f.beta #[x]).eta unfold) |> headBetaThroughLet
    let f' ← mkLambdaFVars #[x] fx'
    match fx' with
    | .letE .. => return .letE f'
    | .lam  .. => return .lam f'
    | _ => return .data (← getFunctionData f')

/-- If head function is a let-fvar unfold it and return resulting function.
Return `none` otherwise. -/
def FunctionData.unfoldHeadFVar? (fData : FunctionData) : MetaM (Option Expr) := do
  let .fvar id := fData.fn | return none
  let some val ← id.getValue? | return none
  let f ← withLCtx fData.lctx fData.insts do
    mkLambdaFVars #[fData.mainVar] (headBetaThroughLet (Mor.mkAppN val fData.args))
  return f

/-- Type of morphism application. -/
inductive MorApplication where
  /-- Of the form `⇑f` i.e. missing argument. -/
  | underApplied
  /-- Of the form `⇑f x` i.e. morphism and one argument is provided. -/
  | exact
  /-- Of the form `⇑f x y ...` i.e. additional applied arguments `y ...`. -/
  | overApplied
  /-- Not a morphism application. -/
  | none
  deriving Inhabited, BEq

/-- Is function body of `f` a morphism application? What kind? -/
def FunctionData.isMorApplication (f : FunctionData) : MetaM MorApplication := do
  if let some name := f.fn.constName? then
    if ← Mor.isCoeFunName name then
      let info ← getConstInfo name
      let arity := info.type.getNumHeadForalls
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underApplied
  match h : f.args.size with
  | 0 => return .none
  | n + 1 =>
    if f.args[n].coe.isSome then
      return .exact
    else if f.args.any (fun a => a.coe.isSome) then
      return .overApplied
    else
      return .none


/-- Decomposes `fun x ↦ f y₁ ... yₙ` into `(fun g ↦ g yₙ) ∘ (fun x y ↦ f y₁ ... yₙ₋₁ y)`

Returns none if:
  - `n=0`
  - `yₙ` contains `x`
  - `n=1` and `(fun x y ↦ f y)` is identity function i.e. `x=f` -/
def FunctionData.peeloffArgDecomposition (fData : FunctionData) : MetaM (Option (Expr × Expr)) := do
  unless fData.args.size > 0 do return none
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return none

    if fData.args.size = 1 &&
       fData.mainVar == fData.fn then
      return none

    let gBody' := Mor.mkAppN fData.fn fData.args[:n-1]
    let gBody' := if let some coe := yₙ.coe then coe.app gBody' else gBody'
    let g' ← mkLambdaFVars #[x] gBody'
    let f' := Expr.lam `f (← inferType gBody') (.app (.bvar 0) (yₙ.expr)) default
    return (f',g')

/-- The result of `FunctionData.decomposition`. -/
inductive DecompositionResult
  /-- The function can be decomposed in a non-trivial way. -/
  | comp (f g : Expr)
  /-- The function is in uncurried form. -/
  | uncurried
  /-- The decomposition failed for some other reason. -/
  | failed

/-- Decompose function `f = (← fData.toExpr)` into composition of two functions. -/
def FunctionData.decomposition (fData : FunctionData) : MetaM DecompositionResult := do

    let mut lctx := fData.lctx
    let insts := fData.insts

    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName

    let fn := fData.fn
    let mut args := fData.args

    if fn.containsFVar xId then
      let .some (f, g) ← fData.peeloffArgDecomposition | return .failed
      return .comp f g

    let mut yVals : Array Expr := #[]
    let mut yVars : Array Expr := #[]

    for argId in fData.mainArgs do
      let yVal := args[argId]!

      let yVal' := yVal.expr
      let yId ← withLCtx lctx insts mkFreshFVarId
      let yType ← withLCtx lctx insts (inferType yVal')
      if yType.containsFVar fData.mainVar.fvarId! then
        return .failed
      lctx := lctx.mkLocalDecl yId (xName.appendAfter (toString argId)) yType
      let yVar := Expr.fvar yId
      yVars := yVars.push yVar
      yVals := yVals.push yVal'
      args := args.set! argId ⟨yVar, yVal.coe⟩

    let g  ← withLCtx lctx insts do
      mkLambdaFVars #[x] (← mkProdElem yVals)
    let f ← withLCtx lctx insts do
      (mkLambdaFVars yVars (Mor.mkAppN fn args))
      >>=
      mkUncurryFun yVars.size

    -- check if is non-triviality
    let f' ← fData.toExpr
    if ← withReducibleAndInstances <| isDefEq f' f then
      return .uncurried
    if ← withReducibleAndInstances <| isDefEq f' g then
      return .failed

    return .comp f g


/-- Decompose function `fun x ↦ f y₁ ... yₙ` over specified argument indices `#[i, j, ...]`.

The result is:
```
(fun (yᵢ',yⱼ',...) ↦ f y₁ .. yᵢ' .. yⱼ' .. yₙ) ∘ (fun x ↦ (yᵢ, yⱼ, ...))
```

This is not possible if `yₗ` for `l ∉ #[i,j,...]` still contains `x`.
In such case `none` is returned.
-/
def FunctionData.decompositionOverArgs (fData : FunctionData) (args : Array Nat) :
    MetaM (Option (Expr × Expr)) := do

  unless isOrderedSubsetOf fData.mainArgs args do return none
  unless ¬(fData.fn.containsFVar fData.mainVar.fvarId!) do return none

  withLCtx fData.lctx fData.insts do

  let gxs := args.map (fun i => fData.args[i]!.expr)

  try
    let gx ← mkProdElem gxs -- this can crash if we have dependent types
    let g ← withLCtx fData.lctx fData.insts <| mkLambdaFVars #[fData.mainVar] gx

    withLocalDeclD `y (← inferType gx) fun y => do

      let ys ← mkProdSplitElem y gxs.size
      let args' := (args.zip ys).foldl (init := fData.args)
          (fun args' (i,y) => args'.set! i { expr := y, coe := args'[i]!.coe })

      let f ← mkLambdaFVars #[y] (Mor.mkAppN fData.fn args')
      return (f,g)
  catch _ =>
    return none

end Meta.FunProp

end Mathlib
