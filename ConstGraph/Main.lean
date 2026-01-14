module

public import Lean
import Mathlib.Lean.Expr.Basic

open Lean Std

def Lean.Environment.isBlackListed (env : Environment) (nm : Name) : Bool :=
  let m := StateM Environment
  let _ : MonadEnv m := { getEnv := get, modifyEnv := modify }
  let go : m Bool := nm.isBlackListed
  go.run' env

public def computeDAG : IO (HashMap Name (HashSet Name)) := do
  initSearchPath (← findSysroot)
  IO.eprintln "Loading environment"
  let env ← importModules #[{ module := `Mathlib }] {}
  IO.eprintln "Computing idx maps"
  let mut constToIdx : HashMap Name Nat := {}
  for (n, _) in env.constants do
    if env.isBlackListed n then continue
    constToIdx := constToIdx.insert n <| constToIdx.size
  let mut idxToConst : HashMap Nat Name := {}
  for (a,b) in constToIdx do
    idxToConst := idxToConst.insert b a
  let mut childrenAux : HashMap Nat (Array Nat) := {}
  IO.eprintln "Computing descendants"
  for (n, c) in env.constants do
    if env.isBlackListed n then continue
    for m in c.type.getUsedConstantsAsSet do
      if env.isBlackListed m then continue
      let n := constToIdx.getD n 0
      let m := constToIdx.getD m 0
      childrenAux := childrenAux.insert m <| childrenAux.getD m #[] |>.push n
  let mut children : HashMap Nat (HashSet Nat) := {}
  for (n, a) in childrenAux do
    children := children.insert n (HashSet.ofArray a |>.filter (· != n))
  let mut out : HashMap Name (HashSet Name) := {}
  for (a,bs) in children do
    out := out.insert (idxToConst.getD a default) <| .ofArray <| bs.toArray.map fun m =>
      idxToConst.getD m default
  return out

/-- Compute all descendants of a constant `a` in the DAG.
A constant `b` is a descendant of `a` if there is a path from `a` to `b` in the DAG,
or if `b = a`. Uses BFS for O(V + E) complexity on the reachable subgraph. -/
public def descendants (a : Name) (dag : HashMap Name (HashSet Name)) : IO (HashSet Name) := do
  let mut visited : HashSet Name := {}
  let mut queue : Array Name := #[a]
  let mut idx := 0
  while idx < queue.size do
    let current := queue[idx]!
    idx := idx + 1
    if visited.contains current then continue
    visited := visited.insert current
    if let some children := dag[current]? then
      for child in children do
        if !visited.contains child then
          queue := queue.push child
  return visited

/-- Compute the induced subgraph of the DAG restricted to descendants of `a`.
Returns a DAG containing only nodes reachable from `a` and edges between them. -/
public def descendantsDAG (a : Name) (dag : HashMap Name (HashSet Name)) :
    IO (HashMap Name (HashSet Name)) := do
  let desc ← descendants a dag
  let mut subgraph : HashMap Name (HashSet Name) := {}
  for node in desc do
    if let some children := dag[node]? then
      let filteredChildren := children.filter desc.contains
      if !filteredChildren.isEmpty then
        subgraph := subgraph.insert node filteredChildren
  return subgraph

/-- Compute the leaves of the descendants subgraph of `a`.
Leaves are descendants that have no outgoing edges within the subgraph. -/
public def descendantsLeaves (a : Name) (dag : HashMap Name (HashSet Name)) :
    IO (HashSet Name) := do
  let desc ← descendants a dag
  let subgraph ← descendantsDAG a dag
  -- Leaves are descendants that don't appear as keys in the subgraph
  -- (i.e., they have no children within the descendants)
  return desc.filter fun node => !subgraph.contains node

public def main : IO UInt32 := do
  let d ← computeDAG
  let leaves ← descendantsLeaves `CategoryTheory.types d
  for leaf in leaves do
    println! leaf
  return 0
