/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Std.Data.Nat.Lemmas
import Std.Lean.Expr


/-!
## `fprop` missing function from standard library
-/

namespace Mathlib
open Lean Meta

namespace Meta.FProp


set_option autoImplicit true

/-- Check if `a` can be obtained by removing elemnts from `b`. -/
def _root_.Array.isOrderedSubsetOf {α} [Inhabited α] [DecidableEq α] (a b : Array α) : Bool := Id.run do
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

def _root_.Lean.Meta.letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) :
    MetaM α :=
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (λ x => do pure ¬(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

def _root_.Lean.Meta.letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr)
    (k : Array Expr → Expr → n α) : n α :=
  map2MetaM (fun k => letTelescopeImpl e k) k

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.modArgRev (modifier : Expr → Expr) (i : Nat) (e : Expr) : Expr :=
  match i, e with
  |      0, .app f x => .app f (modifier x)
  | (i'+1), .app f x => .app (modArgRev modifier i' f) x
  | _, _ => e

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.modArg (modifier : Expr → Expr) (i : Nat) (e : Expr)
    (n := e.getAppNumArgs) : Expr :=
  Expr.modArgRev modifier (n - i - 1) e

-- TODO: fix the implementation in STD
def _root_.Lean.Expr.setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modArg (fun _ => x) i n

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
def mkProdElem (xs : Array Expr) : MetaM Expr := mkAppFoldrM ``Prod.mk xs

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

/-- -/
def mkProdSplitElem (xs : Expr) (n : Nat) : MetaM (Array Expr) :=
  (Array.mkArray n 0)
    |>.mapIdx (λ i _ => i.1)
    |>.mapM (λ i => mkProdProj xs i n)

/-- -/
def mkUncurryFun (n : Nat) (f : Expr) : MetaM Expr := do
  if n ≤ 1 then
    return f
  forallBoundedTelescope (← inferType f) n λ xs _ => do
    let xProdName : String ← xs.foldlM (init:="") λ n x =>
      do return (n ++ toString (← x.fvarId!.getUserName).eraseMacroScopes)
    let xProdType ← inferType (← mkProdElem xs)

    withLocalDecl xProdName default xProdType λ xProd => do
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
