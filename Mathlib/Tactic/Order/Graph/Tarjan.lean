import Mathlib.Tactic.Order.Graph.Basic

namespace Mathlib.Tactic.Order.Graph

structure TarjanState extends DFSState where
  id : Array Nat
  lowlink : Array Nat
  stack : Array Nat
  onStack : Array Bool
  time : Nat

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

def findSCCsImp (g : Graph) : StateM TarjanState Unit := do
  for v in [:g.size] do
    if !(← get).visited[v]! then
      tarjanDFS g v

def findSCCs (g : Graph) : Array Nat :=
  let s : TarjanState := {
    visited := mkArray g.size false
    id := mkArray g.size 0
    lowlink := mkArray g.size 0
    stack := #[]
    onStack := mkArray g.size false
    time := 0
  }
  (findSCCsImp g).run s |>.snd.lowlink

end Mathlib.Tactic.Order.Graph
