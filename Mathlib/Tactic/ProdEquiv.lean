/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Lean.Expr.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Associativity of products

This file constructs a term elaborator for "obvious" equivalences between iterated products.
For example,
```lean
prod_assoc((α × β) × (γ × δ), α × (β × γ) × δ)
```
gives the "obvious" equivalence between `(α × β) × (γ × δ)` and `α × (β × γ) × δ`.
-/

namespace Lean.Expr

open Lean Meta

/-- A helper type to keep track of universe levels and types in iterated produts. -/
inductive ProdTree where
  | type (tp : Expr) (l : Level)
  | prod (fst snd : ProdTree) (lfst lsnd : Level)
deriving Repr

/-- The iterated product corresponding to a `ProdTree`. -/
def ProdTree.getType : ProdTree → Expr
  | type tp _ => tp
  | prod fst snd u v => mkAppN (.const ``Prod [u,v]) #[fst.getType, snd.getType]

/-- The number of types appearing in an iterated product encoded as a `ProdTree`. -/
def ProdTree.size : ProdTree → Nat
  | type _ _ => 1
  | prod fst snd _ _ => fst.size + snd.size

/-- Make a `ProdTree` out of an `Expr`. -/
def mkProdTree (e : Expr) : MetaM ProdTree :=
  match e with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← inferType X).type? | throwError "Not a type{indentExpr X}"
      return .type X u

/-- Given `P : ProdTree` representing an iterated product and `e : Expr` which
should correspond to a term of the iterated product, this will return
a list, whose items correspond to the leaves of `P` (i.e. the types appearing in the product),
where each item is the appropriate composition of `Prod.fst` and `Prod.snd` applied to `e`
resulting in an element of the type corresponding to the leaf.

For example, if `P` corresponds to `(X × Y) × Z` and `t : (X × Y) × Z`, then this
should return `[t.fst.fst, t.fst.snd, t.snd]`.
-/
def ProdTree.unpack (t : Expr) : ProdTree → MetaM (List Expr)
  | type _ _ => return [t]
  | prod fst snd u v => do
      let fst' ← fst.unpack <| mkAppN (.const ``Prod.fst [u,v]) #[fst.getType, snd.getType, t]
      let snd' ← snd.unpack <| mkAppN (.const ``Prod.snd [u,v]) #[fst.getType, snd.getType, t]
      return fst' ++ snd'

/-- This function should act as the "reverse" of `ProdTree.unpack`, constructing
a term of the iterated product out of a list of terms of the types appearing in the product. -/
def ProdTree.pack (ts : List Expr) : ProdTree → MetaM Expr
  | type tp _ => do
    match ts with
      | [] => throwError "Can't pack the empty list."
      | [a] =>
        if ← isDefEq tp (← inferType a) then return a
        else throwError m!"Type error: {a} must have type {tp}."
      | _ => throwError "Failed to pack due to size mismatch."
  | prod fst snd u v => do
    let fstSize := fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed to pack due to size mismatch."
    let tsfst := ts.toArray[:fstSize] |>.toArray.toList
    let tssnd := ts.toArray[fstSize:] |>.toArray.toList
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getType]
    return .app (.app mk (← fst.pack tsfst)) (← snd.pack tssnd)

/-- Given two expressions corresponding to iterated products of the same types, associated in
possibly different ways, this constructs the "obvious" function from one to the other. -/
def mkProdFun (a b : Expr) : MetaM Expr := do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  return .lam `t a (← pb.pack <| (← pa.unpack <| .bvar 0)) .default

/-- Construct the equivalence between iterated products of the same type, associated
in possibly different ways. -/
def mkProdEquiv (a b : Expr) : MetaM Expr := do
  let some u := (← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const ``rfl [.succ u]) a,
      .app (.const ``rfl [.succ v]) b]


/-- An elaborator version of `Lean.Expr.mkEquiv`. -/
elab "prod_assoc(" a:term "," b:term ")" : term => do
  let a ← Elab.Term.elabTerm a none
  let b ← Elab.Term.elabTerm b none
  mkProdEquiv a b

#check prod_assoc(Nat,Nat)

end Lean.Expr
#lint
