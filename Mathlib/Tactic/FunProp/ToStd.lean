/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

/-!
## `funProp` missing function from standard library
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp
set_option autoImplicit true

/-- Check if `a` can be obtained by removing elements from `b`. -/
def isOrderedSubsetOf {α} [Inhabited α] [DecidableEq α] (a b : Array α) : Bool :=
  Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for j in [0:b.size] do
    if i = a.size then
      break

    if a[i]! = b[j]! then
      i := i+1

  if i = a.size then
    return true
  else
    return false

private def letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α :=
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (fun x ↦ do pure ¬(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

/-- Telescope consuming only let bindings -/
def letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr)
    (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => letTelescopeImpl e k) k

/--
  Swaps bvars indices `i` and `j`

  NOTE: the indices `i` and `j` do not correspond to the `n` in `bvar n`. Rather
  they behave like indices in `Expr.lowerLooseBVars`, `Expr.liftLooseBVars`, etc.

  TODO: This has to have a better implementation, but I'm still beyond confused with how bvar
  indices work
-/
def _root_.Lean.Expr.swapBVars (e : Expr) (i j : Nat) : Expr :=

  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray

/--
For `#[x₁, .., xₙ]` create `(x₁, .., xₙ)`.
-/
def mkProdElem (xs : Array Expr) : MetaM Expr := do
  match xs.size with
  | 0 => return default
  | 1 => return xs[0]!
  | _ =>
    let n := xs.size
    xs[0:n-1].foldrM (init:=xs[n-1]!) fun x p => mkAppM ``Prod.mk #[x,p]

/--
For `(x₀, .., xₙ₋₁)` return `xᵢ` but as a product projection.

We need to know the total size of the product to be considered.

For example for `xyz : X × Y × Z`
  - `mkProdProj xyz 1 3` returns `xyz.snd.fst`.
  - `mkProdProj xyz 1 2` returns `xyz.snd`.
-/
def mkProdProj (x : Expr) (i : Nat) (n : Nat) : MetaM Expr := do
  -- let X ← inferType x
  -- if X.isAppOfArity ``Prod 2 then
  match i, n with
  | _, 0 => pure x
  | _, 1 => pure x
  | 0, _ => mkAppM ``Prod.fst #[x]
  | i'+1, n'+1 => mkProdProj (← withTransparency .all <| mkAppM ``Prod.snd #[x]) i' n'

/-- For an element of a product type(of size`n`) `xs` create an array of all possible projections
i.e. `#[xs.1, xs.2.1, xs.2.2.1, ..., xs.2..2]` -/
def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) :=
  (Array.range n)
    |>.mapM (λ i => mkProdProj xs i n)

/-- Uncurry function `f` in `n` arguments. -/
def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallBoundedTelescope (← inferType f) n λ xs _ => do
    let xProdName : String ← xs.foldlM (init:="") λ n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl (.mkSimple xProdName) default xProdType λ xProd => do
      let xs' ← mkProdSplitElem xProd n
      mkLambdaFVars #[xProd] (← mkAppM' f xs').headBeta


/-- Eta expand `f` in only one variable and reduce in others.

Examples:
```
  f                ==> fun x => f x
  fun x y => f x y ==> fun x => f x
  HAdd.hAdd y      ==> fun x => HAdd.hAdd y x
  HAdd.hAdd        ==> fun x => HAdd.hAdd x
``` -/
def etaExpand1 (f : Expr) : MetaM Expr := do
  let f := f.eta
  if f.isLambda then
    return f
  else
    withDefault do forallBoundedTelescope (← inferType f) (.some 1) fun xs _ => do
      mkLambdaFVars xs (mkAppN f xs)
