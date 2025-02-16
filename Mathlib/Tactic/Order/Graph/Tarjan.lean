import Mathlib.Tactic.Order.Graph.Basic

namespace Mathlib.Tactic.Order.Graph

/-- State for the DFS algorithm used to compute the exit times (`tout`) of each vertex. -/
structure FindToutDFSState extends DFSState where
  /-- When the algorithm completes, `tout[v]` stores the exit time of vertex `v`. -/
  tout : Array Nat
  /-- Current time, incremented every time the DFS exits a vertex. -/
  time : Nat

/-- DFS algorithm for computing the exit times of each vertex. -/
partial def findToutDFS (g : Graph) (v : Nat) : StateM FindToutDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true}
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited[u]! then
      findToutDFS g u
  modify fun s => {s with tout := s.tout.set! v s.time}
  modify fun s => {s with time := s.time + 1}

/-- Implementation of `findTout`. -/
def findToutImp (g : Graph) : StateM FindToutDFSState Unit := do
  for v in [:g.size] do
    if !(← get).visited[v]! then
      findToutDFS g v

/-- Computes the exit times of each vertex in a DFS traversal starting at vertex `0`. -/
def findTout (g : Graph) : Array Nat :=
  let s : FindToutDFSState := {
    visited := mkArray g.size false
    tout := mkArray g.size 0
    time := 0
  }
  (findToutImp g).run s |>.snd.tout

/-- Given exit times `tout`, compute the topological ordering of the graph. -/
def toutToTopSort (tout : Array Nat) : Array Nat := Id.run do
  let nVertexes := tout.size
  let mut res := mkArray nVertexes 0
  for v in [:nVertexes] do
    res := res.set! (nVertexes - tout[v]! - 1) v
  return res

/-- State for the DFS algorithm used to compute the condensation of the graph. -/
structure CondenseDFSState extends DFSState where
  /-- When the algorithm completes, `condensation[v]` stores the index of a vertex representing the
  strongly connected component containing `v`. -/
  condensation : Array Nat

/-- DFS algorithm for computing the condensation of the graph. -/
partial def condenseDFS (g : Graph) (c : Nat) (v : Nat) : StateM CondenseDFSState Unit := do
  modify fun s => {s with visited := s.visited.set! v true, condensation := s.condensation.set! v c}
  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited[u]! then
      condenseDFS g c u

/-- Implementation of `condense`. -/
def condenseImp (g : Graph) (order : Array Nat) : StateM CondenseDFSState Unit := do
  for v in order do
    if !(← get).visited[v]! then
      condenseDFS g v v

/-- Computes the condensation of the given graph. The returned array at index `v` contains the index
of the strongly connected component that includes `v`. The numbering of components is arbitrary. -/
def condense (graph : Graph) : Array Nat :=
  let tout := findTout graph
  let order := toutToTopSort tout
  let s : CondenseDFSState := {
    visited := mkArray graph.size false
    condensation := mkArray graph.size graph.size
  }
  let graphInv := inverseGraph graph
  (condenseImp graphInv order).run s |>.snd.condensation

end Mathlib.Tactic.Order.Graph
