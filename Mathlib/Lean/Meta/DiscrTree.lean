/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.DiscrTree
import Mathlib.Lean.Expr.Traverse

/-!
# Additions to `Lean.Meta.DiscrTree`
-/

set_option autoImplicit true

namespace Lean.Meta.DiscrTree

/--
Inserts a new key into a discrimination tree,
but only if it is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific [BEq α] (d : DiscrTree α s)
    (keys : Array (DiscrTree.Key s)) (v : α) : DiscrTree α s :=
  if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

/--
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches (d : DiscrTree α s) (e : Expr) : MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | _ =>
    e.foldlM (fun a f => do pure <| a ++ (← d.getSubexpressionMatches f)) (← d.getMatch e).reverse

variable {m : Type → Type} [Monad m]


/-- The explicit stack of `Trie.mapArrays` -/
private inductive Ctxt {α β s}
  | empty : Ctxt
  | ctxt : Array (Key s × Trie β s) → Array β → Array (Key s × Trie α s) → Key s → Ctxt → Ctxt

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArrays (t : Trie α s) (f : Array α → Array β) : Trie β s :=
  let .node vs0 cs0 := t
  go (.mkEmpty cs0.size) (f vs0) cs0.reverse Ctxt.empty
where
  /-- This implementation as a single tail-recursive function is chosen to not blow the
      interpreter stack when the `Trie` is very deep -/
  go cs vs todo ps :=
    if todo.isEmpty then
      let c := .node vs cs
      match ps with
      | .empty => c
      | .ctxt cs' vs' todo k ps => go (cs'.push (k, c)) vs' todo ps
    else
      let (k, .node vs' cs') := todo.back
      go (.mkEmpty cs'.size) (f vs') cs'.reverse (.ctxt cs vs todo.pop k ps)

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α s) (f : Array α → Array β) : DiscrTree β s :=
  { root := d.root.map (fun t => t.mapArrays f) }

end Lean.Meta.DiscrTree
