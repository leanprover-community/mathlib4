/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

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
    have : n < xs.size := by sorry
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
    
  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"
