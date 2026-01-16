/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.Order.CollectFacts
public meta import Mathlib.Util.AtomM

/-!
# Graphs for the `order` tactic

This module defines the `Graph` structure and basic operations on it. The `order` tactic uses
`≤`-graphs, where the vertices represent atoms, and an edge `(x, y)` exists if `x ≤ y`.
-/

public meta section

namespace Mathlib.Tactic.Order

open Lean Expr Meta

/-- An edge in a graph. In the `order` tactic, the `proof` field stores the of
`atoms[src] ≤ atoms[dst]`. -/
structure Edge where
  /-- Source of the edge. -/
  src : Nat
  /-- Destination of the edge. -/
  dst : Nat
  /-- Proof of `atoms[src] ≤ atoms[dst]`. -/
  proof : Expr

-- For debugging purposes.
instance : ToString Edge where
  toString e := s!"{e.src} ⟶ {e.dst}"

/-- If `g` is a `Graph`, then for a vertex with index `v`, `g[v]` is an array containing
the edges starting from this vertex. -/
abbrev Graph := Std.HashMap Nat (Array Edge)

namespace Graph

/-- Adds an `edge` to the graph. -/
def addEdge (g : Graph) (edge : Edge) : Graph :=
  g.alter edge.src fun | none => #[edge] | some edges => edges.push edge

/-- Constructs a directed `Graph` using `≤` facts. It ignores all other facts. -/
def constructLeGraph (facts : Array AtomicFact) : MetaM Graph := do
  let mut res : Graph := ∅
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
  return res

/-- State for the DFS algorithm. -/
structure DFSState where
  /-- `visited.contains v` if and only if the algorithm has already entered vertex `v`. -/
  visited : Std.HashSet Nat

/-- DFS algorithm for constructing a proof that `x ≤ y` by finding a path from `x` to `y` in the
`≤`-graph. -/
partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : Expr) :
    StateT DFSState MetaM (Option Expr) := do
  modify fun s => {s with visited := s.visited.insert v}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  if !g.contains v then
    return none
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited.contains u then
      match ← buildTransitiveLeProofDFS g u t tExpr with
      | some pf => return some <| ← mkAppM ``le_trans #[edge.proof, pf]
      | none => continue
  return none

/-- Given a `≤`-graph `g`, finds a proof of `s ≤ t` using transitivity. -/
def buildTransitiveLeProof (g : Graph) (s t : Nat) :
    AtomM (Option Expr) := do
  let state : DFSState := ⟨∅⟩
  (buildTransitiveLeProofDFS g s t ((← get).atoms[t]!)).run' state

end Graph

end Mathlib.Tactic.Order
