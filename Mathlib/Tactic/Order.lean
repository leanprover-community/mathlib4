/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Basic
import Qq

/-!
# `order` tactic

This module defines the `order` tactic that is a decision procedure for `Preorder`, `PartialOrder`,
and `LinearOrder` theories.

TODO: write more
-/

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/-- Possible relations used in atomic formulas are `x = y`, `x ≠ y`, `x ≤ y`, `¬(x ≤ y)`, `x < y`,
`¬(x < y)`. -/
inductive AtomicRel
| eq | ne | le | nle | lt | nlt
deriving Inhabited, BEq

/-- Structure for storing facts about variables. -/
structure AtomicFact where
  /-- Index of the variable in LHS. -/
  lhs : Nat
  /-- Index of the variable in RHS. -/
  rhs : Nat
  /-- Relation between LHS and RHS. -/
  rel : AtomicRel
  /-- Proof-term of the fact. -/
  proof : Expr
deriving Inhabited

/-- If `g` is `Graph`, then for a vertex with an index `v`, `g[v]` is the array containing edges
starting in this vertex. Edges are just `AtomicFact`s with `.lhs` and `.rhs` are interpreted as a
source and destination. Some functions below may use `.rel` and `.proof` too. -/
abbrev Graph := Array (Array AtomicFact)

-- for debug
instance : ToString AtomicFact where
  toString := fun fa => match fa.rel with
  | .eq => s!"{fa.lhs} = {fa.rhs}"
  | .ne => s!"{fa.lhs} ≠ {fa.rhs}"
  | .le => s!"{fa.lhs} ≤ {fa.rhs}"
  | .lt => s!"{fa.lhs} < {fa.rhs}"
  | .nle => s!"¬ {fa.lhs} ≤ {fa.rhs}"
  | .nlt => s!"¬ {fa.lhs} < {fa.rhs}"

-- TODO: split conjuctions
/-- Collects the facts from the local context. For each presented type `α` the returned map will
contain a pair `(idxToAtom, facts)` where the map `idxToAtom` allows to convert indexes to found
atomic expression of type `α`, and `facts` contains all collected `AtomicFact`s about them. -/
def collectFacts (g : MVarId) :
    MetaM <| Std.HashMap Expr <| Std.HashMap Nat Expr × Array AtomicFact := g.withContext do
  let ctx ← getLCtx
  let res : (Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact) ←
  ctx.foldlM (init := Std.HashMap.empty) fun res ldecl => do
    let ⟨0, type, expr⟩ := ← inferTypeQ ldecl.toExpr | return res
    match type with
    | ~q(@Eq $α $x $y) =>
      return update res α x y .eq expr
    | ~q(@LE.le $α $inst $x $y) =>
      return update res α x y .le expr
    | ~q(@LT.lt $α $inst $x $y) =>
      return update res α x y .lt expr
    | ~q(@Ne $α $x $y) =>
      return update res α x y .ne expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        return update res α x y .nle expr
      | ~q(@LT.lt $α $inst $x $y) =>
        return update res α x y .nlt expr
    | _ => return res
  return res.map fun _ (atomToIdx, facts) =>
    let idxToAtom : Std.HashMap Nat Expr := atomToIdx.fold (init := .empty) fun acc key value =>
      acc.insert value key
    (idxToAtom, facts)
where update (res : Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact) (type x y : Expr)
    (rel : AtomicRel) (expr : Expr) : Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact :=
  let res := res.insertIfNew type (Std.HashMap.empty, #[])
  res.modify type fun (atomToIdx, facts) =>
    let atomToIdx := atomToIdx.insertIfNew x atomToIdx.size
    let atomToIdx := atomToIdx.insertIfNew y atomToIdx.size
    let facts := facts.push <| ⟨atomToIdx.get! x, atomToIdx.get! y, rel, expr⟩
    (atomToIdx, facts)

section Preprocessing

private lemma le_of_eq_symm {α : Type} [Preorder α] {x y : α} (h : x = y) : y ≤ x :=
  le_of_eq (Eq.symm h)

private lemma not_lt_of_not_le {α : Type} [Preorder α] {x y : α} (h : ¬(x ≤ y)) : ¬(x < y) := by
  intro h'
  exact h h'.le

private lemma le_of_not_lt_le {α : Type} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x ≤ y) :
    y ≤ x := by
  rw [not_lt_iff_not_le_or_ge] at h1
  rcases h1 with (h1 | h1)
  · exact False.elim (h1 h2)
  · assumption

/-- Preprocess facts for preorders. Replace `x < y` with two equivalent facts: `x ≤ y` and
`¬ (y ≤ x)`. Replace `x = y` with `x ≤ y`, `y ≤ x` and remove `x ≠ y`. -/
def preprocessFactsPreorder (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact.rel with
    | .lt =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_lt #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .nle, ← mkAppM ``not_le_of_lt #[fact.proof]⟩
    | .eq =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_eq #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_eq_symm #[fact.proof]⟩
    | .ne =>
      continue
    | _ =>
      res := res.push fact
  return res

/-- Preprocess facts for partial orders. Replace `x < y`, `¬ (x ≤ y)`, and `x = y` with
equivalent facts involving only `≤`, `≠`, and `≮`. -/
def preprocessFactsPartial (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact.rel with
    | .lt =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``LT.lt.ne #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``LT.lt.le #[fact.proof]⟩
    | .nle =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``ne_of_not_le #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .nlt, ← mkAppM ``not_lt_of_not_le #[fact.proof]⟩
    | .eq =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_eq #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_eq_symm #[fact.proof]⟩
    | _ =>
      res := res.push fact
  return res

/-- Preprocess facts for linear orders. Replace `x < y`, `¬ (x ≤ y)`, `¬ (x < y)` and `x = y` with
equivalent facts involving only `≤` and `≠`. -/
def preprocessFactsLinear (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact.rel with
    | .lt =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``LT.lt.ne #[fact.proof]⟩
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``LT.lt.le #[fact.proof]⟩
    | .nle =>
      res := res.push ⟨fact.lhs, fact.rhs, .ne, ← mkAppM ``ne_of_not_le #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_not_ge #[fact.proof]⟩
    | .nlt =>
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_not_lt #[fact.proof]⟩
    | .eq =>
      res := res.push ⟨fact.lhs, fact.rhs, .le, ← mkAppM ``le_of_eq #[fact.proof]⟩
      res := res.push ⟨fact.rhs, fact.lhs, .le, ← mkAppM ``le_of_eq_symm #[fact.proof]⟩
    | _ =>
      res := res.push fact
  return res

end Preprocessing

/-- Construct directed `Graph` using only `≤`-facts. -/
def constructLeGraph (nVertexes : Nat) (facts : Array AtomicFact) :
    Graph := Id.run do
  let mut res : Graph := Array.mkArray nVertexes #[]
  for fact in facts do
    if fact.rel == .le then
      res := res.modify fact.lhs fun edges => edges.push fact
  return res

/-- Inverse the edges of `g`. It swaps `lhs` and `rhs` in each edge, and does nothing with `rel` and
`proof` fields. -/
def inverseGraph (g : Graph) : Graph := Id.run do
  let mut res := Array.mkArray g.size #[]
  for v in [:g.size] do
    for edge in g[v]! do
      res := res.modify edge.rhs fun edges => edges.push ⟨edge.rhs, edge.lhs, edge.rel, edge.proof⟩
  return res

/-- State for the DFS algorithm. -/
structure DFSState where
  /-- `visited[v] = true` iff the algorithm already entered the vertex `v`. -/
  visited : Array Bool

/-- State for the DFS algorithm for computing times of leaving each vertex (`tout`). -/
structure FindToutDFSState extends DFSState where
  tout : Array Nat
  time : Nat

/-- DFS algorithm for computing times of leaving each vertex. -/
partial def findToutDFS (g : Graph) (v : Nat) : StateM FindToutDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true}
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      findToutDFS g u
  modify fun s => {s with tout := s.tout.set! v s.time}
  modify fun s => {s with time := s.time + 1}

def findToutImp (g : Graph) : StateM FindToutDFSState Unit := do
  for v in [:g.size] do
    if !(← get).visited[v]! then
      findToutDFS g v

/-- Find times of leaving each vertex in DFS traversal starting at vertex `0`. -/
def findTout (g : Graph) : Array Nat :=
  let s : FindToutDFSState := {
    visited := mkArray g.size false
    tout := mkArray g.size 0
    time := 0
  }
  (findToutImp g).run s |>.snd.tout

/-- Givin `tout` compute the topological sorting of a graph. -/
def toutToTopSort (tout : Array Nat) : Array Nat := Id.run do
  let nVertexes := tout.size
  let mut res := mkArray nVertexes 0
  for v in [:nVertexes] do
    res := res.set! (nVertexes - tout[v]! - 1) v
  return res

/-- State for the DFS algorithm for computing condensation of the graph. -/
structure CondenseDFSState extends DFSState where
  /-- When the algorithm completes, `condensation[v]` is the index of a vertex that represents a
  strongly connected component containing `v`. -/
  condensation : Array Nat

/-- DFS algorithm for computing condensation of the graph. -/
partial def condenseDFS (g : Graph) (c : Nat) (v : Nat) : StateM CondenseDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true, condensation := s.condensation.set! v c}
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      condenseDFS g c u

def condenseImp (g : Graph) (order : Array Nat) : StateM CondenseDFSState Unit := do
  for v in order do
    if !(← get).visited[v]! then
      condenseDFS g v v

/-- Find condensation of `graph`. The returned array at index `v` contains the number of strongly
connected component that contains `v`. Numeration of components can be arbitrary. -/
def condense (graph : Graph) : Array Nat :=
  let tout := findTout graph
  let order := toutToTopSort tout
  let s : CondenseDFSState := {
    visited := mkArray graph.size false
    condensation := mkArray graph.size graph.size
  }
  let graphInv := inverseGraph graph
  (condenseImp graphInv order).run s |>.snd.condensation

/-- Find the `≠`-fact which `lhs` and `rhs` are in the same strongly connected component of the
`≤`-graph (and then must be equal). -/
def findContradictoryNe (graph : Graph) (facts : Array AtomicFact) : Option AtomicFact :=
  let condensation := condense graph
  facts.find? fun fact =>
    match fact.rel with
    | .ne => condensation[fact.lhs]! == condensation[fact.rhs]!
    | _ => false

/-- DFS algorithm for finding the proof that `x ≤ y` by finding the path from `x` to `y` in
`≤`-graph. -/
partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : Expr) :
    StateT DFSState MetaM (Option Expr) := do
  modify fun s => {s with visited := s.visited.set! v true}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  for edge in g[v]! do
    let u := edge.rhs
    if !(← get).visited[u]! then
      match ← buildTransitiveLeProofDFS g u t tExpr with
      | .some pf => return .some <| ← mkAppM ``le_trans #[edge.proof, pf]
      | .none => continue
  return .none

/-- Using `≤`-graph `g` find the proof of `s ≤ t` by transitivity. -/
def buildTransitiveLeProof (g : Graph) (s t : Nat) (tExpr : Expr) : MetaM (Option Expr) := do
  let state : DFSState := ⟨mkArray g.size false⟩
  (buildTransitiveLeProofDFS g s t tExpr).run' state

/-- TODO -/
def updateGraphWithNlt (g : Graph) (idxToAtom : Std.HashMap Nat Expr) (facts : Array AtomicFact) :
    MetaM Graph := do
  let nltFacts := facts.filter fun fact => match fact.rel with | .nlt => true | _ => false
  let mut used : Array Bool := mkArray nltFacts.size false
  let mut g := g
  while true do
    let mut changed : Bool := false
    for i in [:nltFacts.size] do
      if used[i]! then
        continue
      let fact := nltFacts[i]!
      let .some pf ← buildTransitiveLeProof g fact.lhs fact.rhs (idxToAtom.get! fact.rhs) | continue
      changed := true
      used := used.set! i true
      let newFact : AtomicFact := ⟨fact.rhs, fact.lhs, .le,
        ← mkAppM ``le_of_not_lt_le #[fact.proof, pf]⟩
      g := g.modify fact.rhs fun edges => edges.push newFact
    if !changed then
      break
  return g

/-- Using `≤`-graph `g` finds the contradiction with some `≰`-fact. -/
def findContradictionWithNle (g : Graph) (idxToAtom : Std.HashMap ℕ Expr)
    (facts : Array AtomicFact) : MetaM <| Option Expr := do
  for fact in facts do
    if fact.rel != .nle then
      continue
    let .some pf ← buildTransitiveLeProof g fact.lhs fact.rhs
      (idxToAtom.get! fact.rhs) | continue
    return .some <| mkApp fact.proof pf
  return .none

/-- Types of supported orders: linear, partial, preorder. -/
inductive OrderType
| lin | part | pre
deriving BEq

def findBestInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return .some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return .some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return .some .pre
  return .none

/-- Finishing tactic for solving goals in arbitrary `Preorder`, `PartialOrder` or `LinearOrder`. -/
elab "order" : tactic => focus do
  let g ← getMainGoal
  let .some g ← g.falseOrByContra | return
  setGoals [g]
  let TypeToAtoms ← collectFacts g
  g.withContext do
  for (type, (idxToAtom, facts)) in TypeToAtoms do
    let .some orderType ← findBestInstance type | continue
    let facts : Array AtomicFact ← match orderType with
    | .lin => preprocessFactsLinear g facts
    | .part => preprocessFactsPartial g facts
    | .pre => preprocessFactsPreorder g facts
    let mut graph := constructLeGraph idxToAtom.size facts
    if orderType != .lin then
      graph ← updateGraphWithNlt graph idxToAtom facts
    if orderType == .pre then
      let .some pf ← findContradictionWithNle graph idxToAtom facts | continue
      g.assign pf
      return
    else
      let .some contNe := findContradictoryNe graph facts | continue
      let .some pf1 ← buildTransitiveLeProof graph contNe.lhs contNe.rhs
        (idxToAtom.get! contNe.rhs) | throwError "bug"
      let .some pf2 ← buildTransitiveLeProof graph contNe.rhs contNe.lhs
        (idxToAtom.get! contNe.lhs) | throwError "bug"
      let pf3 ← mkAppM ``le_antisymm #[pf1, pf2]
      g.assign <| mkApp contNe.proof pf3
      return
  throwError "No contradiction found"

end Mathlib.Tactic.Order
