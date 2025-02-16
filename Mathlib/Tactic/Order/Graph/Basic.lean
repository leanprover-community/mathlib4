import Mathlib.Tactic.Order.CollectFacts

namespace Mathlib.Tactic.Order

open Lean Expr Meta

structure Edge where
  src : Nat
  dst : Nat
  proof : Expr

instance : ToString Edge where
  toString e := s!"{e.src} ⟶ {e.dst}"

/-- TODO -/
abbrev Graph := Array (Array Edge)

namespace Graph

def addEdge (g : Graph) (edge : Edge) : Graph :=
  g.modify edge.src fun edges => edges.push edge

/-- Constructs a directed `Graph` using only `≤` facts. -/
def constructLeGraph (nVertexes : Nat) (facts : Array AtomicFact)
    (idxToAtom : Std.HashMap Nat Expr) : MetaM Graph := do
  let mut res : Graph := Array.mkArray nVertexes #[]
  for fact in facts do
    if let .le lhs rhs proof := fact then
      res := res.addEdge ⟨lhs, rhs, proof⟩
    else if let .isTop idx := fact then
      for i in [:nVertexes] do
        if i != idx then
          res := res.addEdge ⟨i, idx, ← mkAppOptM ``le_top #[none, none, none, idxToAtom.get! i]⟩
    else if let .isBot idx := fact then
      for i in [:nVertexes] do
        if i != idx then
          res := res.addEdge ⟨idx, i, ← mkAppOptM ``bot_le #[none, none, none, idxToAtom.get! i]⟩
  return res

/-- Inverts the edges of `g`. This swaps `lhs` and `rhs` in each edge and does nothing to the `rel`
and `proof` fields. -/
def inverseGraph (g : Graph) : Graph := Id.run do
  let mut res : Graph:= Array.mkArray g.size #[]
  for v in [:g.size] do
    for edge in g[v]! do
      res := res.addEdge ⟨edge.dst, edge.src, edge.proof⟩
  return res

/-- State for the DFS algorithm. -/
structure DFSState where
  /-- `visited[v] = true` if and only if the algorithm has already entered vertex `v`. -/
  visited : Array Bool

/-- DFS algorithm for constructing a proof that `x ≤ y` by finding a path from `x` to `y` in the
`≤`-graph. -/
partial def buildTransitiveLeProofDFS (g : Graph) (v t : Nat) (tExpr : Expr) :
    StateT DFSState MetaM (Option Expr) := do
  modify fun s => {s with visited := s.visited.set! v true}
  if v == t then
    return ← mkAppM ``le_refl #[tExpr]
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited[u]! then
      match ← buildTransitiveLeProofDFS g u t tExpr with
      | .some pf => return .some <| ← mkAppM ``le_trans #[edge.proof, pf]
      | .none => continue
  return .none

/-- Given a `≤`-graph `g`, finds a proof of `s ≤ t` using transitivity. -/
def buildTransitiveLeProof (g : Graph) (idxToAtom : Std.HashMap Nat Expr) (s t : Nat) :
    MetaM (Option Expr) := do
  let state : DFSState := ⟨mkArray g.size false⟩
  (buildTransitiveLeProofDFS g s t (idxToAtom.get! t)).run' state

end Graph

end Mathlib.Tactic.Order
