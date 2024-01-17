/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Lean.Expr.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Associativity of products

This file constructs a term elaborator for "obvious" equivalences between iterated products.
For example,
```lean
(prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)
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

/-- The components of an interated product, presented as a `ProdTree`. -/
def ProdTree.components : ProdTree → List Expr
  | type tp _ => [tp]
  | prod fst snd _ _ => fst.components ++ snd.components

/-- Make a `ProdTree` out of an `Expr`. -/
partial def mkProdTree (e : Expr) : MetaM ProdTree :=
  match e.consumeMData with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← whnfD <| ← inferType X).type? | throwError "Not a type{indentExpr X}"
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
  | type _ _ => do
    match ts with
      | [] => throwError "Can't pack the empty list."
      | [a] => return a
      | _ => throwError "Failed due to size mismatch."
  | prod fst snd u v => do
    let fstSize := fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed due to size mismatch."
    let tsfst := ts.toArray[:fstSize] |>.toArray.toList
    let tssnd := ts.toArray[fstSize:] |>.toArray.toList
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getType]
    return .app (.app mk (← fst.pack tsfst)) (← snd.pack tssnd)

/-- Converts a term `e` in an iterated product `P1` into a term of an iterated product `P2`.
Here `e` is an `Expr` representing the term, and the iterated products are represented
by terms of `ProdTree`. -/
def ProdTree.convertTo (P1 P2 : ProdTree) (e : Expr) : MetaM Expr :=
  return ← P2.pack <| ← P1.unpack e

/-- Given two expressions corresponding to iterated products of the same types, associated in
possibly different ways, this constructs the "obvious" function from one to the other. -/
def mkProdFun (a b : Expr) : MetaM Expr := do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  unless pa.components.length == pb.components.length do
    throwError "The number of components in{indentD a}\nand{indentD b}\nmust match."
  for (x,y) in pa.components.zip pb.components do
    unless ← isDefEq x y do
      throwError "Component{indentD x}\nis not definitionally equal to component{indentD y}."
  withLocalDeclD `t a fun fvar => do
    mkLambdaFVars #[fvar] (← pa.convertTo pb fvar)

/-- Construct the equivalence between iterated products of the same type, associated
in possibly different ways. -/
def mkProdEquiv (a b : Expr) : MetaM Expr := do
  let some u := (← whnfD <| ← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← whnfD <| ← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const ``rfl [.succ u]) a,
      .app (.const ``rfl [.succ v]) b]

/-- IMPLEMENTATION: Syntax used in the implementation of `prod_assoc%`.
This elaborator postpones if there are metavariables in the expected type,
and to propagate the fact that this elaborator produces an `Equiv`,
the `prod_assoc%` macro sets things up with a type ascription.
This enables using `prod_assoc%` with, for example `Equiv.trans` dot notation. -/
syntax (name := prodAssocStx) "prod_assoc_internal%" : term

open Elab Term in
/-- Elaborator for `prod_assoc%`. -/
@[term_elab prodAssocStx]
def elabProdAssoc : TermElab := fun stx expectedType? => do
  match stx with
  | `(prod_assoc_internal%) => do
    let some expectedType ← tryPostponeIfHasMVars? expectedType?
          | throwError "expected type must be known"
    let .app (.app (.const ``Equiv _) a) b := expectedType
          | throwError "Expected type{indentD expectedType}\nis not of the form `α ≃ β`."
    mkProdEquiv a b
  | _ => throwUnsupportedSyntax

/--
`prod_assoc%` elaborates to the "obvious" equivalence between iterated products of types,
regardless of how the products are parenthesized.
The `prod_assoc%` term uses the expected type when elaborating.
For example, `(prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)`.

The elaborator can handle holes in the expected type,
so long as they eventually get filled by unification.
```lean
example : (α × β) × (γ × δ) ≃ α × (β × γ) × δ :=
  (prod_assoc% : _ ≃ α × β × γ × δ).trans prod_assoc%
```
-/
macro "prod_assoc%" : term => `((prod_assoc_internal% : _ ≃ _))

end Lean.Expr
