/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Init.ZeroOne
import Mathlib.Data.ListM.Basic

/-!
# A^* search

This implementation is only intended for use in meta code, rather than algorithmic analysis.
Someone might enjoy writing a "mathematical" version.
-/

open Std
variable (m : Type u → Type u) [Monad m] [Alternative m]
  (P V E : Type u) [Ord P] [Zero P] [Add P] [BEq V] [Hashable V]

namespace AStar

section GraphData

/-- Representation of a path in a graph for A^* search. We cache the priority. -/
structure Path where
  prio : P
  to : V
  edges : List E

/--
Data structure encoding a graph for A^* search.

This records the source and target of each directed edge,
the edges leaving each vertex (as a lazy list),
the weight of each edge,
and the heuristic distance to a goal for each vertex.
-/
structure GraphData where
  s : E → V
  t : E → V
  nbhd : V → ListM m E
  weight : E → P
  heuristic : V → P

variable {m P V E}

/-- Add an edge to a path. -/
def cons (Γ : GraphData m P V E) (e : E) (p : Path P V E) : Path P V E :=
{ prio := Γ.weight e + p.prio,
  to := Γ.t e,
  edges := e :: p.edges }

end GraphData

/--
Data associated to a vertex during A^* search.
We record the best seen path so far, and track which edges are `explored` and `remaining`.
-/
structure VertexData [Inhabited P] [Inhabited V] [Inhabited E] where
  bestPath : Path P V E
  heuristicPrio : P
  totalPrio : P
  explored : List E
  remaining : ListM m E

variable [Inhabited P] [Inhabited V] [Inhabited E]

/-- This inhabited instance doesn't really make sense,
but is needed to write `partial` functions below. -/
instance : Inhabited (VertexData m P V E) :=
  ⟨{ bestPath := { prio := default, to := default, edges := [] },
     heuristicPrio := default
     totalPrio := default
     explored := []
     remaining := .nil }⟩

/--
Mutable state during A^* search.

We maintain a priority queue as a red-black tree backed multimap from priorities to vertices.
We additionally maintain vertex data
(consisting of priority, best yet path, and explored/remaining edges)
for each vertex visited so far.
-/
structure State where
  queue : RBMap P (List V) compare
  data : HashMap V (VertexData m P V E)

/-- State monad for A^* search. -/
abbrev M := StateT (State m P V E) m

variable {m P V E}

/--
Record a new path.
* If the ending vertex has not been seen before, build new `VertexData`,
  and add the vertex to the queue.
* If the ending vertex has been seen before, and this path is no better than the previous best path,
  do nothing.
* If this is better than the previous best path:
  * Move the ending vertex up in the priority queue
  * Record it as the new best path
  * And, if we are searching for optimal solutions (i.e. paths with shortest length),
    recursively record all paths obtained by adding a previously explored edge to this path.
-/
partial def recordPath (Γ : GraphData m P V E) (optimal : Bool) (path : Path P V E) :
    (M m P V E) PUnit := do
  let σ ← get
  let v := path.to
  match σ.data.find? v with
  | none => do
    let heuristicPrio := Γ.heuristic v
    let totalPrio := path.prio + heuristicPrio
    let d : VertexData m P V E :=
    { bestPath := path
      heuristicPrio := heuristicPrio
      totalPrio := totalPrio
      explored := []
      remaining := Γ.nbhd v }
    let σ' : State m P V E :=
    { queue := σ.queue.alter totalPrio fun L? => L?.map (v :: ·) |>.getD [v],
      data := σ.data.insert v d }
    set σ'
  | some d => if (compare path.prio d.bestPath.prio).isLT then
      let totalPrio := path.prio + d.heuristicPrio
      let d' : VertexData m P V E :=
      { d with
        bestPath := path
        totalPrio := totalPrio }
      let σ' : State m P V E :=
      { queue := σ.queue.alter d.totalPrio (fun L? => L?.map fun L => L.erase v)
          |>.alter totalPrio fun L? => L?.map (v :: ·) |>.getD [v],
        data := σ.data.insert v d' }
      set σ'
      if optimal then for e in d.explored do
        recordPath Γ optimal (cons Γ e path)

/-- Return the vertex data for the first vertex in the priority queue. -/
partial def readMin : M m P V E (VertexData m P V E) := do
  let σ ← get
  match σ.queue.min with
  | none => failure
  | some (p, []) => do
      -- No nodes left at the lowest priority, remove that priority from the queue and try again.
      set { σ with queue := σ.queue.erase p }
      readMin
  | some (_, v :: _) => match σ.data.find? v with
    | none => failure -- shouldn't be possible: everything in the queue has data
    | some d => pure d

/-- Obtain the next remaining edge leaving the highest priority vertex in the queue,
updating the `explored` and `remaining` fields of `VertexData` at the same time. -/
partial def nextEdge : M m P V E (VertexData m P V E × E) := do
  let σ ← get
  match σ.queue.min with
  | none => failure
  | some (p, []) => do
      -- No nodes left at the lowest priority, remove that priority from the queue and try again.
      set { σ with queue := σ.queue.erase p }
      nextEdge
  | some (p, v :: others) => match σ.data.find? v with
    | none => failure -- shouldn't be possible: everything in the queue has data
    | some d => do match ← (uncons (d.remaining) : m _) with
      | none => do
          -- No neighbours left to explore, remove this vertex from the queue and try again.
          set { σ with queue := σ.queue.insert p others }
          nextEdge
      | some (e, remaining) => do
          -- Update the explored and remaining edges at this vertex, and return the edge.
          let d' := { d with explored := e :: d.explored, remaining := remaining }
          set { σ with data := σ.data.insert v d' }
          pure (d', e)

/-- Perform one step of A^* search:
mark the next edge leaving the highest priority vertex `v` as explored,
and record the path obtained by adding the edge to the best yet path to `v`. -/
def update (Γ : GraphData m P V E) (optimal : Bool) :
    (M m P V E) PUnit := do
  let (d, e) ← nextEdge
  recordPath Γ optimal (cons Γ e d.bestPath)

end AStar

variable {m P V E}
variable [Inhabited P] [Inhabited V] [Inhabited E]

open AStar

/--
Perform A^* search on a graph, starting from a given vertex.

The graph should be encoded using `AStar.GraphData`.

If the option `optimal` is false,
then we don't update best paths when a shorter path is found to an already visited vertex.
If the heuristic is "consistent", this will never happen.
However if the heuristic is "admissible" but not "consistent",
`optimal` must be true if you want the shortest path.
(In practice, the heuristic is often neither consistent nor admissible,
and you will need to test whether `optimal` is suitable for your requirements.)

Returns a monadic lazy list consisting of triples `(priority, vertex, path)`
for each vertex we explore an edge from. `path` is the best path so far to that vertex.

See also `aStarSearch` which just provides the solution,
rather than all the partial solutions explored along the way.
-/
def aStarSearchPaths (Γ : GraphData m P V E) (optimal : Bool) (v : V) :
    ListM m (P × V × List E) :=
let p := Γ.heuristic v
let d : VertexData m P V E :=
  { bestPath := { to := v, edges := [], prio := 0 },
    heuristicPrio := p,
    totalPrio := p,
    explored := [],
    remaining := Γ.nbhd v }
let σ : State m P V E :=
  { queue := RBMap.single 0 [v],
    data := HashMap.empty.insert v d }
ListM.iterate (do update Γ optimal; readMin)
  |>.runState' σ |>.map fun d => ⟨d.totalPrio, d.bestPath.to, d.bestPath.edges⟩

/--
Perform A^* search on a graph,
starting at a vertex `src` and ending when reaching a vertex satisfying `goal`.

Note that the `goal` is probably also implicitly described in the `Γ : GraphData m P V E`
argument, as it must produce the heuristic estimates of distance to goal.

If the option `optimal` is false,
then we don't update best paths when a shorter path is found to an already visited vertex.
(See the doc-string for `aStarSearchPaths` for details.)

Returns a list of edges, wrapped in the same monad the graph edges are generated in.

See also `aStarSearchPaths` which iterates through
all paths explored on the way to finding the solution.
-/
def aStarSearch (Γ : GraphData m P V E) (optimal : Bool) (src : V) (goal : V → Bool) :
    m (List E) :=
aStarSearchPaths Γ optimal src |>.filter (goal ·.2.1) |>.map (·.2.2) |>.head

-- PROJECT rather than computing distances, compute lower bounds on distances,
-- which are refined when a vertex reaches the head of the queue.

-- PROJECT bidirectional A^* search?
