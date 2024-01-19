/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Std.Data.Nat.Lemmas
import Std.Lean.Expr
import Mathlib.Tactic.FProp.ArraySet

import Qq

namespace Mathlib
open Lean Meta

namespace Meta.FProp


set_option autoImplicit true

/-- -/
def joinlM [Monad m] [Inhabited β] (xs : Array α) (map : α → m β) (op : β → β → m β) : m β := do
  if h : 0 < xs.size then
    xs[1:].foldlM (init:=(← map xs[0])) λ acc x => do op acc (← map x)
  else
    pure default

/-- -/
def joinl [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  joinlM xs map op

/-- -/
def joinrM [Monad m] [Inhabited β] (xs : Array α) (map : α → m β) (op : β → β → m β) : m β := do
  if h : 0 < xs.size then
    let n := xs.size - 1
    have : n < xs.size := by apply Nat.sub_one_lt_of_le h (by simp)
    xs[0:n].foldrM (init:=(← map xs[n])) λ x acc => do op (← map x) acc 
  else
    pure default

/-- -/
def joinr [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  joinrM xs map op

/-- -/
def mkAppFoldrM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    joinrM xs pure
      λ x p =>
        mkAppM const #[x,p]

/-- -/
def mkAppFoldlM (const : Name) (xs : Array Expr) : MetaM Expr := do
  if xs.size = 0 then
    return default
  if xs.size = 1 then
    return xs[0]!
  else
    joinlM xs pure
      λ p x =>
        mkAppM const #[p,x]

/--
For `#[x₁, .., xₙ]` create `(x₁, .., xₙ)`.
-/
def mkProdElem (xs : Array Expr) (mk := ``Prod.mk) : MetaM Expr := mkAppFoldrM mk xs

/--
For `(x₀, .., xₙ₋₁)` return `xᵢ` but as a product projection.

We need to know the total size of the product to be considered.

For example for `xyz : X × Y × Z`
  - `mkProdProj xyz 1 3` returns `xyz.snd.fst`.
  - `mkProdProj xyz 1 2` returns `xyz.snd`.
-/
def mkProdProj (x : Expr) (i : Nat) (n : Nat) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM Expr := do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM snd #[x]) i' n'

/-- -/
def mkProdSplitElem (xs : Expr) (n : Nat) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Array Expr) := 
  (Array.mkArray n 0)
    |>.mapIdx (λ i _ => i.1)
    |>.mapM (λ i => mkProdProj xs i n fst snd)

/-- -/
def mkUncurryFun (n : Nat) (f : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallTelescope (← inferType f) λ xs _ => do
    let xs := xs[0:n]

    let xProdName : String ← xs.foldlM (init:="") λ n x => 
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs mk)

    withLocalDecl xProdName default xProdType λ xProd => do
      let xs' ← mkProdSplitElem xProd n fst snd
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta




/--
  Split lambda function into composition by specifying over which auguments in the lambda body this split should be done.
 -/
def splitLambdaToCompOverArgs (e : Expr) (argIds : ArraySet Nat) : MetaM (Option (Expr × Expr)) := do
  let e ← 
    if e.isLambda 
    then pure e
    else do 
      let X := (← inferType e).bindingDomain!
      pure (.lam `x X (.app e (.bvar 0)) default)
    
  match e with 
  | .lam name _ _ _ => 
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x

      let mut fn := b.getAppFn
      let mut args := b.getAppArgs

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut yVals : Array Expr := #[]
      let mut yVars : Array Expr := #[]

      let xIds := xs.map fun x => x.fvarId!
      let xIds' := xIds[1:].toArray
      
      for argId in argIds.toArray do
        let yVal := args[argId]!

        -- abstract over trailing arguments
        let xs'' := xIds'.filterMap (fun xId => if yVal.containsFVar xId then .some (Expr.fvar xId) else .none)
        let yVal' ← mkLambdaFVars xs'' yVal
        let yId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl yId (name.appendAfter (toString argId)) (← inferType yVal')
        let yVar := Expr.fvar yId
        yVars := yVars.push yVar
        yVals := yVals.push yVal'
        args := args.set! argId (mkAppN yVar xs'')

      let g  ← mkLambdaFVars #[x] (← mkProdElem yVals)
      let f ← withLCtx lctx instances do
        (mkLambdaFVars (yVars ++ xs[1:]) (mkAppN fn args)) 
        >>= 
        mkUncurryFun yVars.size

      -- `f` should not contain `x` and `g` should not contain `xs[1:]` 
      -- if they do then the split is unsuccessful
      if f.containsFVar xIds[0]! then
        return none

      return (f, g)
    
  | _ => return none


/-- Takes lambda function `fun x => b` and splits it into composition of two functions. 

  Example:
    fun x => f (g x)      ==>   f ∘ g 
    fun x => f x + c      ==>   (fun y => y + c) ∘ f
    fun x => f x + g x    ==>   (fun (y₁,y₂) => y₁ + y₂) ∘ (fun x => (f x, g x))
    fun x i => f (g₁ x i) (g₂ x i) i  ==>   (fun (y₁,y₂) i => f y₁ y₂ i) ∘' (fun x i => (g₁ x i, g₂ x i))
    fun x i => x i        ==>   (fun x i => x i) ∘' (fun x i => x)
 -/
def splitLambdaToComp (e : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Expr × Expr) := do
  match e with 
  | .lam name _ _ _ => 
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut ys' : Array Expr := #[]
      let mut zs  : Array Expr := #[]

      if f.containsFVar xId then
        let zId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl zId (name) (← inferType f)
        let z := Expr.fvar zId
        zs  := zs.push z
        ys' := ys'.push f
        f := z

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          let zId ← withLCtx lctx instances mkFreshFVarId
          lctx := lctx.mkLocalDecl zId (name.appendAfter (toString i)) (← inferType y)
          let z := Expr.fvar zId
          zs  := zs.push z
          ys' := ys'.push y
          f := f.app z
        else
          f := f.app y

      let y' ← mkProdElem ys' mk
      let g  ← mkLambdaFVars xs y'

      f ← withLCtx lctx instances (mkLambdaFVars (zs ++ xs[1:]) f)
      f ← mkUncurryFun zs.size f mk fst snd

      return (f, g)
    
  | _ => 
    let XY ← inferType e
    if ¬XY.isForall then
      throwError "can't split {← ppExpr e} not a function!"
    let X := XY.bindingDomain!
    return (e, .lam default X (.bvar 0) default)


structure FunTelescopeConfig where
  /-- telescope through coercions via  -/
  funCoe := false

partial def funTelescopeImpl {α} (f : Expr) (config : FunTelescopeConfig) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let F ← inferType f
  forallTelescope F fun xs B => do

    let b := (mkAppN f xs).headBeta

    if config.funCoe = false then
      k xs b 
    else
      try
        let b' ← mkAppM `FunLike.coe #[b]
        funTelescopeImpl b' config fun xs' b'' => k (xs ++ xs') b''
      catch _ => 
        k xs b

variable [MonadControlT MetaM n] [Monad n]

def funTelescope (e : Expr) (config : FunTelescopeConfig) (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => funTelescopeImpl e config k) k


def constArity (decl : Name) : CoreM Nat := do
  let info ← getConstInfo decl
  return info.type.forallArity
