/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Order.Graph.Basic

/-!
# Tarjan's Algorithm

This file implements Tarjan's algorithm for finding the strongly connected components (SCCs) of
a graph.
-/

namespace Mathlib.Tactic.Order.Graph

/-- State for Tarjan's algorithm. -/
structure TarjanState extends DFSState where
  /-- `id[v]` is the index of the vertex `v` in the DFS traversal. -/
  id : Array Nat
  /-- `lowlink[v]` is the smallest index of any node on the stack that is reachable from `v`
  through `v`'s DFS subtree. -/
  lowlink : Array Nat
  /-- The stack of visited vertices used in Tarjan's algorithm. -/
  stack : Array Nat
  /-- `onStack[v] = true` iff `v` is in `stack`. The structure is used to check it efficiently. -/
  onStack : Array Bool
  /-- A time counter that increments each time the algorithm visits an unvisited vertex. -/
  time : Nat

/-- The Tarjan's algorithm.
See [Wikipedia](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm). -/
partial def tarjanDFS (g : Graph) (v : Nat) : StateM TarjanState Unit := do
  modify fun s => {
    visited := s.visited.set! v true,
    id := s.id.set! v s.time,
    lowlink := s.lowlink.set! v s.time,
    stack := s.stack.push v,
    onStack := s.onStack.set! v true,
    time := s.time + 1
  }

  for edge in g[v]! do
    let u := edge.dst
    if !(← get).visited[u]! then
      tarjanDFS g u
      modify fun s => {s with
        lowlink := s.lowlink.set! v (min s.lowlink[v]! s.lowlink[u]!),
      }
    else if (← get).onStack[u]! then
      modify fun s => {s with
        lowlink := s.lowlink.set! v (min s.lowlink[v]! s.id[u]!),
      }

  if (← get).id[v]! = (← get).lowlink[v]! then
    let mut w := 0
    while true do
      w := (← get).stack.back!
      modify fun s => {s with
        stack := s.stack.pop
        onStack := s.onStack.set! w false
        lowlink := s.lowlink.set! w s.lowlink[v]!
      }
      if w = v then
        break

/-- Implementation of `findSCCs` in the `StateM TarjanState` monad. -/
def findSCCsImp (g : Graph) : StateM TarjanState Unit := do
  for v in [:g.size] do
    if !(← get).visited[v]! then
      tarjanDFS g v

/-- Finds the strongly connected components of the graph `g`. Returns an array where the value at
index `v` represents the SCC number containing vertex `v`. The numbering of SCCs is arbitrary. -/
def findSCCs (g : Graph) : Array Nat :=
  let s : TarjanState := {
    visited := .replicate g.size false
    id := .replicate g.size 0
    lowlink := .replicate g.size 0
    stack := #[]
    onStack := .replicate g.size false
    time := 0
  }
  (findSCCsImp g).run s |>.snd.lowlink


end Mathlib.Tactic.Order.Graph
