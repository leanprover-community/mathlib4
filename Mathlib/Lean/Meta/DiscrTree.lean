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

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches (d : DiscrTree α s) (e : Expr) : MetaM (Array α) := do
  e.foldlM (fun a f => do pure <| a ++ (← d.getSubexpressionMatches f)) (← d.getMatch e).reverse
variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α s) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β s) := do
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α s) (f : Array α → m (Array β)) : m (DiscrTree β s) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α s) (f : Array α → Array β) : DiscrTree β s :=
  d.mapArraysM fun A => (pure (f A) : Id (Array β))

private partial def createNodes (keys : Array (Key s)) (v : Array α → Array α) (i : Nat) : Trie α s :=
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩
    let c := createNodes keys v (i+1)
    .node #[] #[(k, c)]
  else
    .node (v #[]) #[]

private partial def insertAux (keys : Array (Key s)) (v : Array α → Array α) : Nat → Trie α s → Trie α s
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys.get ⟨i, h⟩
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .node vs c
    else
      .node (v vs) cs

def modifyCore (d : DiscrTree α s) (keys : Array (Key s)) (v : Array α → Array α) : DiscrTree α s :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def modify (d : DiscrTree α s) (e : Expr) (v : Array α → Array α) : MetaM (DiscrTree α s) := do
  let keys ← mkPath e
  return d.modifyCore keys v

end Lean.Meta.DiscrTree
