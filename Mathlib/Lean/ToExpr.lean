/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Bhavik Mehta
-/
import Mathlib.Data.Finset.Empty

/-! # Helper functions to create Expr terms for Finsets, Multisets and Sets.

This file provides some basic tools to create an `Expr` term representing a
finset/multiset/set of terms of type `α`, given a `ToExpr` instance on `α`.

-/

universe u

open Lean Meta

/-- A helper function for building `Expr` terms from a list of terms of type `α`. -/
private def List.toExprAux {α} [ToExpr α] (nilFn : Expr)
    (singFn : Expr) (consFn : Expr) : List α → Expr
  | []    => nilFn
  | [a] => .app singFn (toExpr a)
  | a::as => mkApp2 consFn (toExpr a) (List.toExprAux nilFn singFn consFn as)

/-- Produces the `Expr` corresponding to the finset associated to a list.

`List.toFinsetExpr [a, b, c, ...]` is the `Expr` representing the finset
`insert a (insert b (insert c ...))`. -/
def List.toFinsetExpr {α : Type u} [ToExpr α] (l : List α) : MetaM Expr := do
  let t₁ := toTypeExpr α
  let t₂ ← mkAppM ``Finset #[t₁]
  let nil  ← mkAppOptM ``EmptyCollection.emptyCollection #[t₂, none]
  let sing ← mkAppOptM ``Singleton.singleton #[t₁, t₂, none]
  let cons ← mkAppOptM ``Insert.insert #[t₁, t₂, none]
  return l.toExprAux nil sing cons

/-- Produces the `Expr` corresponding to the finset associated to a list.

`List.toMultisetExpr [a, b, c, ...]` is the `Expr` representing the multiset
`insert a (insert b (insert c ...))`. -/
def List.toMultisetExpr {α : Type u} [ToExpr α] (l : List α) : MetaM Expr := do
  let t₁ := toTypeExpr α
  let t₂ ← mkAppM ``Multiset #[t₁]
  let nil  ← mkAppOptM ``EmptyCollection.emptyCollection #[t₂, none]
  let sing ← mkAppOptM ``Singleton.singleton #[t₁, t₂, none]
  let cons ← mkAppOptM ``Insert.insert #[t₁, t₂, none]
  return l.toExprAux nil sing cons

/-- Produces the `Expr` corresponding to the finset associated to a list.

`List.toSetExpr [a, b, c, ...]` is the `Expr` representing the set
`insert a (insert b (insert c ...))`. -/
def List.toSetExpr {α : Type u} [ToExpr α] (l : List α) : MetaM Expr := do
  let t₁ := toTypeExpr α
  let t₂ ← mkAppM ``Set #[t₁]
  let nil  ← mkAppOptM ``EmptyCollection.emptyCollection #[t₂, none]
  let sing ← mkAppOptM ``Singleton.singleton #[t₁, t₂, none]
  let cons ← mkAppOptM ``Insert.insert #[t₁, t₂, none]
  return l.toExprAux nil sing cons
