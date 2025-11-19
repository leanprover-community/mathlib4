/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.Basic
import Mathlib.CategoryTheory.Iso
import Batteries.Data.List.Basic

/-!
# The `Cancelable` structure

This files defines a `Cancelable` structure that stores the data of
an expression, the data of the "inverse" (in the category-theoretic sense) of that expression.
and proofs of the various lemmas used to move the expression "from the lhs to the rhs" using
its inverse.
This file also defines a global reference `cancelableFactoriesRef` which is a list
that stores registered ways to check that a given expression is that of a `Cancelable` and
compute such structure when it is the case.

This structure is part of the `rotate_isos` tactic.

-/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory

namespace Tactic.CategoryTheory.RotateIsos

/-- An expression is cancelable if it has an expression `inv`, and if there are proofs
that
- `∀ {h h'}, expr ≫ h = h' → h = inv ≫ h'`
- `∀ {h h'}, h ≫ expr = h' → h = h' ≫ inv`
- `∀ {h}, expr = h → 𝟙 _ = inv ≫ h`
- `∀ {h}, expr = h → 𝟙 _ = h ≫ inv`.

By working at the `Expr` level, we can actually make sente of cancelable morphisms
both in the case of morphisms and isomorphism (using `Iso.trans` and `Iso.refl` instead of
`Category.comp` and `Category.id`.

The structure `Cancelable` is a book-keeping structure that holds the expression,
an expression of its inverse, as well as expressions of proofs of the lemmas needed to cancel it. -/
structure Cancelable where
  /-- The expression -/
  expr : Expr
  /-- An expression of the inverse of `expr`. -/
  inv : Expr
  /-- An epression of type `∀ {h h'}, expr ≫ h = h' → h = inv ≫ h'`. -/
  eq_inv_comp : Expr
  /-- An epression of type `∀ {h h'}, h ≫ expr = h' → h = h' ≫ inv`. -/
  eq_comp_inv : Expr
  /-- An epression of type `∀ {h}, expr = h → 𝟙 _ = inv ≫ h`. -/
  id_eq_inv_comp : Expr
  /-- An epression of type `∀ {h}, expr = h → 𝟙 _ = h ≫ inv`. -/
  id_eq_comp_inv : Expr

/-- A monad that stores stores the global function that decides if an expression is cancelable. -/
abbrev CancelM := ReaderT (Expr → MetaM (Option Cancelable)) MetaM

/-- Given an expression and a list of ways to produce a cancelable morphism from an
expression, yields the first `Cancelable` structure we can derive from the expression by
applying the given rules. The rules to produce a cancelable morphism may need (e.g for functors)
to get the cancelable structure for subexpressions. -/
partial def getCancelable?Aux (e : Expr)
    (L : CancelM <| List <| Expr → Expr → MetaM (Option Cancelable)) :
    MetaM (Option Cancelable) := do
  let whnfR_e ← whnfR e
  (← L.run (getCancelable?Aux · L)).findSomeM? (do · e whnfR_e)

/-- A reference that stores the currently registered ways of detecting whether or not
a morphisms is cancelable, as well as priority informations. Higher priorities get tried first.
This is necessary to make it so that we can later expand this list in extensions of the tactic
(e.g, for monoidal contexts).
Functions in this list are intended to take as fist argument the expression to simplify,
as second argument its weak head normal form at reducible transparency,
and are intended to return a `Cancelable` in which the `expr` is the first argument passed.

Contract for this variable:
- The list should remain sorted with respect to the second key.
- Duplicate entries should not cause undefined behaviour, but are still intented to be avoided.
- No assumption on order should be made about entries with equal priorities.

The helper functions `insertCancelableFactory` and `insertCancelableFactory'`
take care of inserting functions at their right place, and should be the prefered
way of registering ways to cancel morphisms.
-/
initialize cancelableFactoriesRef :
    IO.Ref <| CancelM <| List <| (Expr → Expr → MetaM (Option Cancelable)) × Nat ←
  IO.mkRef <| pure []

/-- Helper function that registers a function `f : Expr → Expr → MetaM (Option Cancelable)`
as a way to construct `Cancelable` structure.
This function does not check that this do not produce a duplicate entry and caller is responsible
for ensuring first that they are not duplicating an entry.
See the docstring of `cancelableFactoriesRef` for an explanation on the intended behaviour
of functions passed as first argument. -/
def insertCancelableFactory (f : Expr → Expr → MetaM (Option Cancelable)) (p : Nat) : IO Unit :=
  cancelableFactoriesRef.modify fun current =>
    return List.insertP (fun x => p ≥ x.2) (f, p) (← current)

/-- Helper function that registers a function `f : Expr → Expr → CancelM (Option Cancelable)`
as a way to construct `Cancelable` structure.
This function does not check that this do not produce a duplicate entry and caller is responsible
for ensuring first that they are not duplicating an entry.
See the docstring of `cancelableFactoriesRef` for an explanation on the intended behaviour
of functions passed as first argument. -/
def insertCancelableFactory' (f : Expr → Expr → CancelM (Option Cancelable)) (p : Nat) :
      IO Unit :=
  cancelableFactoriesRef.modify fun current => do
    let c ← read
    return List.insertP (fun x => p ≥ x.2) (fun e w => (f e w).run c, p) (← current)

/-- Given an expression `e`, if `e` is an expression for a cancelable morphism, returns
a `Cancelable` structure such that `e.expr` is the original expression using the rules to do
so that are currently in context. Otherwise, returns `none`. -/
def getCancelable? (e : Expr) : MetaM (Option Cancelable) := do
  getCancelable?Aux e <| (← cancelableFactoriesRef.get).bind (fun x => return x.map Prod.fst)

open _root_.CategoryTheory in
/-- Given an expression of type `f₁ ≫ ⋯ ≫ fₙ`or `f₁ ≪≫ ⋯ ≪≫ fₙ`
assumed to be either fully left-associated or right-associated
(depending on the argument `rev_assoc`),
build a list of the cancelable morphisms (with their cancellation data) starting from
the leftmost or rightmost morphism (depending on the argument `rev`) until we hit a
non-cancelable term.
The function also returns a flag that is set if all of the morphisms are cancelable. -/
partial def getCancelables (e : Expr) (rev rev_assoc: Bool) : MetaM (List Cancelable × Bool) := do
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, l, r])
  | (``Iso.trans, #[_, _, _, _, _, l, r]) =>
    match rev_assoc, rev with
    | true, true =>
      -- expression is left-associated and we look at morphisms from left to right
      let (t, b) ← getCancelables l rev rev_assoc
      if b then
        if let some c ← getCancelable? r then return (t ++ [c], b)
        else return (t, false)
      else return (t, false)
    | true, false =>
      -- expression is left-associated and we look at morphisms from right to left
      if let some c ← getCancelable? r then
        let (t, b) ← getCancelables l rev rev_assoc
        return (c::t, b)
      else return ([], False)
    | false, true =>
      -- expression is right-associated and we look at morphisms from right to left
      let (t, b) ← getCancelables r rev rev_assoc
      if b then
        if let some c ← getCancelable? l then return (t ++ [c], b)
        else return (t, false)
      else return (t, false)
    | false, false =>
      -- expression is right-associated and we look at morphisms from left to right
      if let some c ← getCancelable? l then
        let (t, b) ← getCancelables r rev rev_assoc
        return (c::t, b)
      else return ([], false)
  | _ => if let some c ← getCancelable? e then return ([c], true) else return ([], false)

end Tactic.CategoryTheory.RotateIsos
