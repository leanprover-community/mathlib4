/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/

import Lean
-- import SciLean.Tactic.LSimp.Main
-- import SciLean.Tactic.DataSynth.Decl
-- import SciLean.Lean.Meta.Uncurry
-- import SciLean.Lean.Meta.Basic

-- import Mathlib.Logic.Equiv.Defs
-- import Mathlib.Tactic.DataSynth.Decl
import Mathlib.Tactic.FunProp.ToBatteries

open Lean Meta

namespace Mathlib.Meta.DataSynth

open Mathlib.Meta.FunProp

/-- Structure representing function of the form

```
let y₁ := ..; ...; let yₘ := ...;
fun (x₁,...,xₙ) => b
```
where `leadingLets := #[y₁,...,yₘ]`, `xs := #[x₁,...,xₙ]` and `body := b`

`body` is and expresion of containing free/let variables `y₁,...,yₘ,x₁,...,xₙ` which are well
defined in the local context `lctx` and `insts`.
-/
structure FunData where
  lctx : LocalContext
  insts : LocalInstances
  leadingLets : Array Expr
  xs : Array Expr
  body : Expr
  deriving Inhabited


/-- Turn function `f` into `FunData`b. -/
def getFunData (f : Expr) : MetaM FunData := do
  letTelescope f fun ys f => do
  curryLambdaTelescope (← etaExpand1 f) fun xs b => do
    let data : FunData :=
      { lctx := ← getLCtx
        insts := ← getLocalInstances
        leadingLets := ys
        xs := xs
        body := ← withConfig (fun cfg => {cfg with zeta:=false, zetaDelta:=false}) <|
          whnfR <| b }
    return data

namespace FunData

-- def pp (f : FunData) : MetaM String :=
--   withLCtx f.lctx f.insts do
--     let xnames ← f.xs.mapM ppExpr
--     let binder :=
--       if f.xs.size = 1 then
--         xnames[0]!
--       else
--         "(" ++ xnames.joinl id (· ++ ", " ++ ·) ++ ")"
--     return s!"fun {binder} => {← ppExpr f.body}"


/-- Return `fun ((x₁,x₂,...,xₙ) : X₁×X₂×...×Xₙ) => f x₁ ... xₙ)` -/
def toExpr (f : FunData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    mkUncurryLambdaFVars f.xs f.body
    >>=
    mkLambdaFVars f.leadingLets

/-- Returnns `(fun (x₁ : X₁) ((x₂,...,xₙ) : X₂×...×Xₙ) => f x₁ ... xₙ)` -/
def toExprCurry1 (f : FunData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    mkLambdaFVars #[f.xs[0]!] (← mkUncurryLambdaFVars f.xs[1:] f.body (withLet:=false))
    >>=
    mkLambdaFVars f.leadingLets

inductive FunHead where
  | bvar (i : Nat)
  | fvar (id : FVarId)
  | app
  | letE
  | lam
  | unimplemented
  deriving Repr

/-- Head of the function body. -/
def funHead (f : FunData) : MetaM FunHead :=
  match f.body with
  | .const .. | .proj .. | .app .. => return .app
  | .fvar xId =>
    let x := Expr.fvar xId
    if let .some i := f.xs.findIdx? (fun x' => x == x') then
      return .bvar i
    else
      return .fvar xId
  | .letE .. => return .letE
  | .lam .. => return .lam
  | .sort .. | .mdata .. | .mvar .. | .forallE .. | .bvar .. | .lit .. =>
    withLCtx f.lctx f.insts do
      throwError "invalid function body, ctor:{f.body.ctorName}\n{← ppExpr f.body}"

/-- For function `f` representing `fun ((x₁,x₂,...,xₙ) : X₁×X₂×...×Xₙ) (y : Y) => f x₁ ... xₙ) y`
    return `y` as free variables and `fun ((x₁,x₂,...,xₙ) : X₁×X₂×...×Xₙ) => f x₁ ... xₙ) y`
    i.e. removes `y` binder in the body. -/
def bodyLambdaTelescope1 (f : FunData) (k : Expr → FunData → DataSynthM α) : DataSynthM α := do
  withLCtx f.lctx f.insts do
    let .lam n t b bi  := f.body
      | throwError "FunData.introBodyLambda: expected lambda in the function body {←f.pp}"
    withLocalDecl n bi t fun y => do
      let f : FunData := {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        leadingLets := f.leadingLets
        xs := f.xs
        body := b.instantiate1 y
      }
      k y f

def lambdaTelescope1 (f : FunData) (k : Expr → FunData → DataSynthM α) : DataSynthM α := do
  withLCtx f.lctx f.insts do
    k f.xs[0]! {f with xs := f.xs[1:]}

-- /-- Composition of two function.-/
-- inductive FunDecomp where
-- /-- Standard composition of `f` and `g` as `f∘g` -/
-- | comp (f g : FunData)
-- /-- Composition through letbinding, `fun x => let y := g x; f y x` -/
-- | letE (f g : FunData)
-- | none

/-- If function body has leading let binding we distinguish three cases. -/
inductive BodyLetCase where
/-- Function is in the form
```
fun x =>
  let y := g x
  f y
```
i.e. body of let does not depend on `x`-/
| comp (f g : FunData)
/-- Function is in the form
```
fun x =>
  let y := g x
  f y x
```
let binding in its generality.

Returned `f` is a function in `y,x₁,...,xₙ` for `x = (x₁,...,xₙ)`. -/
| letE (f g : FunData)
/-- Function is in the form
```
fun x =>
  let y := v
  f y x
```
or
```
fun x =>
  let y := v
  f x
```
i.e. value of let binding does not depend on the function argument or body of let does not depend on the let value
-/
| simple (f : FunData)

def getBodyLetCase (f : FunData) : MetaM BodyLetCase := do
  let .letE n t v b _ := f.body | panic! "getBodyLetCase error: function body is expected to contain let binding!"

  -- let binding is not used so we just remove it
  if ¬b.hasLooseBVars then
    return .simple {f with body := b}

  withLCtx f.lctx f.insts do

  let v ← withConfig (fun cfg => {cfg with zeta:=false, zetaDelta:=false}) <|
    whnfR v

  -- let binding is just an fvar, it is uninteresting so we ignore it!
  -- this is a case for example when having `f : FunData` that reprents this function
  --   `fun xy : X×X => let x := xy.1; let y := xy.2; x + y`
  -- the first two should be ignored as `f` stores this function curried form
  --   `fun x y => let x' := (x,y).1; let y' := (x,y).2; x' + y'`
  -- thus these let bindings reduce to `let x' := x` and `let y' := y` and are uninteresting
  if v.isFVar then
    return .simple {f with body := b.instantiate1 v}

  -- does expression `e` contain any of the input variables `xᵢ`?
  let containsX (e : Expr) : Bool := (e.hasAnyFVar (fun id => f.xs.contains (.fvar id)))

  -- test for simple case
  -- does `v` has any of the `xᵢ` vars in it?
  if ¬(containsX v) then
    withLetDecl n t v fun y => do
      return .simple {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        leadingLets := f.leadingLets.push y
        xs := f.xs
        body := b.instantiate1 y
      }
  else
    if ¬(containsX b) then
       return .comp
         (← withLocalDecl n .default t fun y => do pure {
           lctx := ← getLCtx
           insts := ← getLocalInstances
           leadingLets := f.leadingLets
           xs := #[y]
           body := b.instantiate1 y
         })
         { -- g
           lctx := ← getLCtx
           insts := ← getLocalInstances
           leadingLets := f.leadingLets
           xs := f.xs
           body := v
         }
    else
       return .letE
         (← withLocalDecl n .default t fun y => do pure {
           lctx := ← getLCtx
           insts := ← getLocalInstances
           leadingLets := f.leadingLets
           xs := #[y] ++ f.xs
           body := b.instantiate1 y
         })
         { -- g
           lctx := ← getLCtx
           insts := ← getLocalInstances
           leadingLets := f.leadingLets
           xs := f.xs
           body := v
         }


-- /-- Decompose function as composition of two functions. -/
-- def decompose (f : FunData) : MetaM FunDecomp := do
--   withLCtx f.lctx f.insts do
--     let .letE n t v b _ := f.body | return .none

--     let g : FunData := {
--       lctx := f.lctx
--       insts := f.insts
--       xs := f.xs
--       body := v
--     }

--     withLocalDeclD n t fun y => do
--       let f : FunData := {
--         lctx := ← getLCtx
--         insts := f.insts
--         xs := #[y] ++ f.xs
--         body := b.instantiate1 y
--       }

--       return .letE f g


/-- Given a function `f : X → Y` find
`p₁ : X → X₁`, `p₂ : X → X₂` and `q : X₁ → X₂`  and `g : X₁ → Y`  -/
def decomposeDomain? (f : FunData) : MetaM (Option (Expr × Expr × Expr × FunData)) := do
  withLCtx f.lctx f.insts do

    if f.xs.size ≤ 1 then
      return none

    let vars := (← f.body.collectFVars |>.run {}).2.fvarSet
    let (xs₁, xs₂) := f.xs.partition (fun x => vars.contains x.fvarId!)

    if xs₂.size = 0 then
      return none

    let g : FunData := {f with xs := xs₁}

    let p₁ ←
      mkUncurryLambdaFVars f.xs (← mkProdElem xs₁) (withLet:=false)
    let p₂ ←
      mkUncurryLambdaFVars f.xs (← mkProdElem xs₂) (withLet:=false)

    let q ←
      mkUncurryLambdaFVars xs₂ (← mkProdElem f.xs) (withLet:=false)
      >>=
      mkUncurryLambdaFVars xs₁ (withLet:=false)

    return some (p₁,p₂,q,g)


/-- Tries to write function `fun (x₁,...,xₙ) => f x₁ ... x₂` as composition of two non-trivial functions. -/
def nontrivialAppDecomposition (fData : FunData) : MetaM (Option (FunData × FunData)) := do
  withLCtx fData.lctx fData.insts do
  match fData.body with
  | .proj t i b => do

    if (fData.xs.size = 1) ∧ (b == fData.xs[0]!) then return .none

    let f : FunData := ← withLocalDeclD `x (← inferType b) fun x => do pure {
      lctx := ← getLCtx
      insts := ← getLocalInstances
      leadingLets := #[]
      xs := #[x]
      body := .proj t i x
    }

    let g : FunData := {
      lctx := fData.lctx
      insts := fData.insts
      leadingLets := fData.leadingLets
      xs := fData.xs
      body := b
    }

    return .some (f,g)

  | .app .. =>

    let fn := fData.body.getAppFn
    let args := fData.body.getAppArgs'

    let containsX (e : Expr) : Bool := (e.hasAnyFVar (fun id => fData.xs.contains (.fvar id)))

    -- we do not currently support cases where the body head depends on `x`
    if containsX fn then return none

    -- figure out which arguments contains `xᵢ`
    let mut depArgIds : Array Nat := #[]
    let mut yVals : Array Expr := #[]
    let mut yNames : Array Name := #[]
    for arg in args, i in [0:args.size] do
      if containsX arg then
        depArgIds := depArgIds.push i
        yVals := yVals.push arg
        yNames := yNames.push (Name.appendAfter `y (toString i))

    -- early return for constant functions
    if depArgIds.size = 0 then return none

    -- gather types and
    withLocalDecls' yNames .default (← yVals.mapM inferType) fun yVars => do

      -- replace values with free variables
      let args' := (depArgIds.zip yVars).foldl (init:=args) (fun args' (i,var) => args'.set! i var)

      let f : FunData := {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        leadingLets := fData.leadingLets
        xs := yVars
        body := ← withConfig (fun cfg => {cfg with zeta:=false, zetaDelta:=false}) <|
          whnfR <| mkAppN fn args'
      }

      let g : FunData := {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        leadingLets := fData.leadingLets
        xs := fData.xs
        body := ← mkProdElem yVals
      }

      -- check nontriviality (there might be a better way of doing this, but this should be fool proof)
      if (← isDefEq (← fData.toExpr) (← f.toExpr)) ||
         (← isDefEq (← fData.toExpr) (← g.toExpr)) then
        return none

      return .some (f,g)
  | _ => return .none


end FunData

end Meta.DataSynth
