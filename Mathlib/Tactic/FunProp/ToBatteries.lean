/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Init

/-!
## `funProp` missing function from standard library
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

/-- Check if `a` can be obtained by removing elements from `b`. -/
def isOrderedSubsetOf {α} [Inhabited α] [DecidableEq α] (a b : Array α) : Bool :=
  Id.run do
  if a.size > b.size then
    return false
  let mut i := 0
  for h' : j in [0:b.size] do
    if i = a.size then
      break

    if a[i]! = b[j] then
      i := i+1

  if i = a.size then
    return true
  else
    return false

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
  match h : xs.size with
  | 0 => return default
  | 1 => return xs[0]
  | n + 1 =>
    xs[0:n].foldrM (init := xs[n]) fun x p => mkAppM ``Prod.mk #[x,p]

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
    |>.mapM (fun i ↦ mkProdProj xs i n)

/-- Uncurry function `f` in `n` arguments. -/
def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallBoundedTelescope (← inferType f) n fun xs _ ↦ do
    let xProdName : String ← xs.foldlM (init:="") fun n x ↦
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl (.mkSimple xProdName) default xProdType fun xProd ↦ do
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

/-- Implementation of `betaThroughLet` -/
private def betaThroughLetAux (f : Expr) (args : List Expr) : Expr :=
  match f, args with
  | f, [] => f
  | .lam _ _ b _, a :: as => (betaThroughLetAux (b.instantiate1 a) as)
  | .letE n t v b nondep, args => .letE n t v (betaThroughLetAux b args) nondep
  | .mdata _ b, args => betaThroughLetAux b args
  | f, args => mkAppN f args.toArray

/-- Apply the given arguments to `f`, beta-reducing if `f` is a lambda expression. This variant
does beta-reduction through let bindings without inlining them.

Example
```
beta' (fun x => let y := x * x; fun z => x + y + z) #[a,b]
==>
let y := a * a; a + y + b
```
-/
def betaThroughLet (f : Expr) (args : Array Expr) : Expr :=
  betaThroughLetAux f args.toList

/-- Beta reduces head of an expression, `(fun x => e) a` ==> `e[x/a]`. This version applies
arguments through let bindings without inlining them.

Example
```
headBeta' ((fun x => let y := x * x; fun z => x + y + z) a b)
==>
let y := a * a; a + y + b
```
-/
def headBetaThroughLet (e : Expr) : Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn true then betaThroughLet f e.getAppArgs else e


end Meta.FunProp

end Mathlib
