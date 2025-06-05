/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Init
import Qq

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

private def letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α :=
  lambdaLetTelescope e fun xs b ↦ do
    if let .some i ← xs.findIdxM? (fun x ↦ do pure !(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

/-- Telescope consuming only let bindings -/
def letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr)
    (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => letTelescopeImpl e k) k

/-- Make local declarations is we have an array of names and types. -/
def mkLocalDecls {n} [MonadControlT MetaM n] [Monad n]
    (names : Array Name) (bi : BinderInfo) (types : Array Expr) :
    Array (Name × BinderInfo × (Array Expr → n Expr)) :=
  types.mapIdx (fun i type => (names[i]!, bi, fun _ : Array Expr => pure type))

/-- Simpler version of `withLocalDecls` that can't deal with dependent types but has simpler
signature -/
def withLocalDecls' {α n} [Inhabited α] [MonadControlT MetaM n] [Monad n]
  (names : Array Name) (bi : BinderInfo) (types : Array Expr) (k : Array Expr → n α) : n α :=
  withLocalDecls (mkLocalDecls names bi types) k

private partial def withLetDeclsImpl {α}
  (names : Array Name) (vals : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  loop #[]
where
  loop (acc : Array Expr) : MetaM α := do
    let i := acc.size
    if h : i < vals.size then
      let val := vals[i]
      let type ← inferType val
      withLetDecl names[i]! type val fun x => loop (acc.push x)
    else
      k acc

/-- Append an array of let free variables `xs` to the local context and execute `k xs`.
`declInfos` takes the form of an array consisting of:
- the name of the variable
- the binder info of the variable
- a type constructor for the variable, where the array consists of all of the free variables
  defined prior to this one. This is needed because the type of the variable may depend on prior variables.

Same as `withLocalDecls` but for let bindings. -/
def withLetDecls {n α} [MonadControlT MetaM n] [Monad n]
  (names : Array Name) (vals : Array Expr) (k : Array Expr → n α) : n α :=
  map1MetaM (fun k => withLetDeclsImpl names vals k) k


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

/-- Size of product type, assuming it is right associated
i.e. `prodSize (A×B×C) = 3` but `prodSize ((A×B)×C) = 2` -/
def prodSize (e : Expr) : Nat :=
  go e 1
where
  go (e : Expr) (n : Nat) :=
    match e with
    | mkApp2 (.const ``Prod _) _ Y =>
      go Y (n+1)
    | _ => n

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

/-- Curry function `f` to `n` arguments.

For example turns `fun x : Nat×Nat => x.1 + x.2 + x.1` into `fun x y : Nat => x + y + x` -/
def mkCurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  else
    let .forallE xName xType _ _ := (← inferType f)
      | throwError "can't curry `{← ppExpr f}` not a function"

    withLocalDecl xName .default xType fun x => do
      let xs ← mkProdSplitElem x n
      let xNames := xs.mapIdx fun i _ => xName.appendAfter (toString i)
      let xTypes ← xs.mapM inferType
      withLocalDecls' xNames .default xTypes fun xVars => do
        let x' ← mkProdElem xVars
        let b := (f.app x').headBeta

        let b ← Meta.transform b
          (post := fun e => do
            if (← isType e)
            then return .done e
            else return .done (reduceProdProj e))

        mkLambdaFVars xVars b
where
  reduceProdProj (e : Expr) : Expr :=
  match e with
  | .proj ``Prod 0 xy
  | mkApp3 (.const ``Prod.fst _) _ _ xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ x _) => x
    | xy => .proj ``Prod 0 xy
  | .proj ``Prod 1 xy
  | mkApp3 (.const ``Prod.snd _) _ _ xy =>
    match reduceProdProj xy with
    | (mkApp4 (.const ``Prod.mk _) _ _ _ y) => y
    | xy => .proj ``Prod 1 xy
  | _ => e


/-- Lamba telescope that curries the first argument of the input function `f`. -/
def curryLambdaTelescope {α} (f : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let .forallE _ xType _ _ := (← inferType f)
    | throwError "can't curry `{← ppExpr f}` not a function"

  let n := prodSize xType
  let f ← mkCurryFun n f

  lambdaBoundedTelescope f n k

/-- Takes expression `b` with free vars `xs = #[x₁, ..., xₙ]` and returns lambda function in one
argument of the form:
```
fun x =>
  let x₁ := x.1
  let x₂ := x.2.1
  ...
  let xₙ := x.2....2
  b
``` -/
def mkUncurryLambdaFVars (xs : Array Expr) (b : Expr) (withLet:=true) : MetaM Expr := do

  if xs.size = 1 then return ← mkLambdaFVars xs b

  let x ← mkProdElem xs
  let X ← inferType x

  let xnames ← xs.mapM (fun x => x.fvarId!.getUserName)

  withLocalDeclD `x X fun xvar => do

    let xvals := mkProdSplitElem' xvar xs.size

    if withLet then
      withLetDecls xnames xvals fun xvars => do
        let b := b.replaceFVars xs xvars
        mkLambdaFVars (#[xvar] ++ xvars) b
    else
      let b := b.replaceFVars xs xvals
      mkLambdaFVars #[xvar] b

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
  | .letE n t v b _, args => .letE n t v (betaThroughLetAux b args) false
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
