/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Qq

/-!
# `order` tactic

This module defines the `order` tactic, a decision procedure for the theories of `Preorder`,
`PartialOrder`, and `LinearOrder`.

## Implementation Details

Below, we describe the algorithm for each type of order. All algorithms begin with two steps:
1. Negate the goal so that our goal now is to derive `False`.
2. Collect the set of *facts*, i.e., atomic expressions in one of six forms: `x = y`, `x ≠ y`,
`x ≤ y`, `¬(x ≤ y)`, `x < y`, and `¬(x < y)`. We then attempt to derive a contradiction from this
set of facts.

### Preorder
3. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with two equivalent facts: `x ≤ y` and `¬(y ≤ x)`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Remove `x ≠ y`.
Note that the last two operations weaken the set of facts.
4. **Building the `≤`-graph**.
We construct a graph where vertices correspond to atoms, and an edge `(x, y)` exists if the fact
`x ≤ y` is present in our set of facts. We call this graph a `≤`-graph.
5. **Growing the `≤`-graph with `≮`-facts**.
In preorders, `¬(x < y)` is equivalent to `(x ≤ y) → (y ≤ x)`. Thus, if `y` is reachable from `x`
in the `≤`-graph, we can derive the new fact `y ≤ x`. At this step, we add such edges to the graph
while possible.
6. **Finding contradictions using `≰`-facts**.
For each fact `¬(x ≤ y)`, we check if `y` is reachable from `x` in the `≤`-graph. If so, we derive
the desired contradiction.

#### Why is this a decision procedure?
Technically, it is not, because it cannot prove `(x = y) → (y ≠ z) → (x ≠ z)`. Goals involving
only `=` and `≠` can be handled by the `cc` tactic. Assume, then, that a set `T` of facts is
contradictory, but there is no chain `x₁ = x₂ = ... = xₖ` in `T` along with the fact `x₁ ≠ xₖ`. Then
we claim that the described algorithm is able to deduce a contradiction from `T`. Let `T'` be the
set of facts after preprocessing. Then `T'` remains contradictory.

Indeed, suppose that `T'` is satisfiable, i.e., there exists a model `M` that satisfies `T'`.
Consider a quotient `M'` of `M` by the equivalence relation `~`, where `a ~ b` holds for `a ≠ b` iff
both `a` and `b` are values of some variables `x` and `y` from `T`, and there is
a chain `x = ... = y` in `T`. Define the relation `R'` on `M'` as `α R' β` if and only if `a R b`
in `M` for some `a ∈ α` and `b ∈ β`. Then `M'` is a model satisfying `T`:
* For any fact `x = y` in `T`, we have `M'(x) = M'(y)` in `M'`.
* For any fact `x ≠ y` in `T`, we have `M'(x) ≠ M'(y)`, since otherwise, there would exist
  a chain `x = ... = y` in `T`.
* For any fact `x ≤ y` in `T`, and thus in `T'`, we have `M(x) R M(y)`, so `M'(x) R' M'(y)`.
* For any fact `¬(x ≤ y)` in `T`, and thus in `T'`, we have `¬M(x) R M(y)`. Then, for any `x' ~ x`
  and `y' ~ y`, we can deduce `x ≤ x'` and `y' ≤ y` from `T'`. If `M(x') R M(y')`, then
  `M(x) R M(x') R M(y') R M(y)`, which contradicts the assumption that `M` is a model of `T'`.
  This contradiction implies that `¬M'(x) R' M'(y)`, as required.

If, at step 6, no contradictory `≰`-facts were found, we must show that a model satisfies `T'`.
A suitable model can be constructed using the connected components of the `=`-graph (defined
similarly to the `≤`-graph),
with the relation `R` defined as `C₁ R C₂` iff `C₂` is reachable from `C₁` in the `≤`-graph. Each
variable `x` is interpreted as its component `[x]`. This forms a preorder, and we verify that each
fact in `T'` is satisfied:
* `x = y` is satisfied because `x` and `y` must be in the same component in the `=`-graph.
* `x ≤ y` is satisfied by the construction of the `≤`-graph.
* `x ≠ y` is satisfied because otherwise, `x` and `y` would belong to the same component in
the `=`-graph, contradicting our initial assumption.
* `¬(x < y)` is satisfied because otherwise `¬[y] R [x]`, meaning there is a path from `x` to `y`,
which would have caused an edge `(y, x)` to be added at step 5, leading to a contradiction.

### Partial Order
3. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with `x ≤ y` and `x ≠ y`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Replace `¬(x ≤ y)` with `x ≠ y` and `¬(x < y)`.
4. **Building the `≤`-graph**: Same as for preorders.
5. **Growing the `≤`-graph with `≮`-facts**: Same as for preorders.
6. **Finding contradictions using `≠`-facts**.
We identify strongly connected components in the `≤`-graph using a standard algorithm. For each
fact `x ≠ y`, we check whether `x` and `y` belong to the same component. If they do, then `x = y` is
provable, contradicting `x ≠ y`.

#### Why is this a decision procedure?
Assume that a set `T` of facts is contradictory. We must show that the described algorithm can
derive a contradiction. Let `T'` be the set of facts after preprocessing. By construction, `T'` is
also contradictory (they are equisatisfiable). If, at step 6, no contradictory `≠`-facts were found,
we must show that a model satisfies `T'`. A suitable model consists of the strongly connected
components of the `≤`-graph, with the relation `R` defined as `C₁ R C₂` iff `C₂` is reachable
from `C₁`. Each variable `x` is interpreted as its component `[x]`. This forms a partial order, and
we verify that each fact in `T'` is satisfied:
* `x ≤ y` is satisfied because it directly implies `[x] R [y]`.
* `x ≠ y` is satisfied because otherwise, `x` and `y` would belong to the same component, leading to
a contradiction at step 6.
* `¬(x < y)` is satisfied because otherwise `[x] ≠ [y]` and there is a path from `x` to `y`, which
would have merged them into the same component at step 5.

### Linear Order
3. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with `x ≤ y` and `x ≠ y`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Replace `¬(x ≤ y)` with `x ≠ y` and `y ≤ x`.
* Replace `¬(x < y)` with `y ≤ x`.
4. **Building the `≤`-graph**: Same as for preorders.
5. **Finding contradictions using `≠`-facts**: Same as for partial orders.

Note that the algorithm for linear orders is simply the algorithm for partial orders with an
additional preprocessing step. It also skips the growing step because there is no `≮`-facts.

#### Why is this a decision procedure?
We need to slightly modify the proof for partial orders. In this case, `T` and `T'` are again
equisatisfiable. Suppose the algorithm cannot find a contradiction, and construct the model of `T'`.
The carrier of the model is once again the set of strongly connected components in the `≤`-graph,
with variables interpreted as their respective components. Note that the reachability relation
(used before) on components is acyclic. Therefore, it can be
[topologically ordered](https://en.wikipedia.org/wiki/Topological_sorting), meaning it forms a
linear order where `C₁ R C₂` whenever `C₂` is reachable from `C₁`. It is easy to see that all facts
in `T'` are satisfied by the model.

-/

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

/-- A structure for storing facts about variables. -/
inductive AtomicFact
| eq (lhs : Nat) (rhs : Nat) (proof : Expr)
| ne (lhs : Nat) (rhs : Nat) (proof : Expr)
| le (lhs : Nat) (rhs : Nat) (proof : Expr)
| nle (lhs : Nat) (rhs : Nat) (proof : Expr)
| lt (lhs : Nat) (rhs : Nat) (proof : Expr)
| nlt (lhs : Nat) (rhs : Nat) (proof : Expr)
| isTop (idx : Nat)
| isBot (idx : Nat)
| isInf (lhs : Nat) (rhs : Nat) (res : Nat) (proof : Expr)
| isSup (lhs : Nat) (rhs : Nat) (res : Nat) (proof : Expr)
deriving Inhabited, BEq

-- For debugging purposes.
instance : ToString AtomicFact where
  toString fa := match fa with
  | .eq lhs rhs _ => s!"{lhs} = {rhs}"
  | .ne lhs rhs _ => s!"{lhs} ≠ {rhs}"
  | .le lhs rhs _ => s!"{lhs} ≤ {rhs}"
  | .nle lhs rhs _ => s!"¬ {lhs} ≤ {rhs}"
  | .lt lhs rhs _ => s!"{lhs} < {rhs}"
  | .nlt lhs rhs _ => s!"¬ {lhs} < {rhs}"
  | .isTop idx => s!"{idx} = ⊤"
  | .isBot idx => s!"{idx} = ⊥"
  | .isInf lhs rhs res _ => s!"{lhs} ⊓ {rhs} = {res}"
  | .isSup lhs rhs res _ => s!"{lhs} ⊔ {rhs} = {res}"

abbrev CollectFactsState := Std.HashMap Expr <| Std.HashMap Expr Nat × Array AtomicFact
abbrev CollectFactsM := StateT CollectFactsState MetaM

def isTop {u : Level} (type : Q(Type u)) (x : Q($type)) : MetaM Bool := do
  try
    let leInst ← synthInstanceQ (q(LE $type))
    let inst ← synthInstanceQ (q(OrderTop $type))
    let top := q((@OrderTop.toTop $type $leInst $inst).top)
    return ← isDefEq x top
  catch _ =>
    return false

def isBot {u : Level} (type : Q(Type u)) (x : Q($type)) : MetaM Bool := do
  try
    let leInst ← synthInstanceQ (q(LE $type))
    let inst ← synthInstanceQ (q(OrderBot $type))
    let bot := q((@OrderBot.toBot $type $leInst $inst).bot)
    return ← isDefEq x bot
  catch _ =>
    return false

def addAtom {u : Level} (type : Q(Type u)) (x : Q($type)) : CollectFactsM Nat := do
  modify fun res => res.insertIfNew type (Std.HashMap.empty, #[])
  modify fun res => res.modify type fun (atomToIdx, facts) =>
    let atomToIdx := atomToIdx.insertIfNew x atomToIdx.size
    (atomToIdx, facts)
  let idx := (← get).get! type |>.fst.get! x
  if ← isTop type x then
    modify fun res => res.modify type fun (atomToIdx, facts) =>
      (atomToIdx, facts.push <| .isTop idx)
  if ← isBot type x then
    modify fun res => res.modify type fun (atomToIdx, facts) =>
      (atomToIdx, facts.push <| .isBot idx)
  return idx

def addFact (type : Expr) (fact : AtomicFact) : CollectFactsM Unit := do
  modify fun res => res.modify type fun (atomToIdx, facts) =>
    let facts := facts.push fact
    (atomToIdx, facts)

def collectFactsImp (g : MVarId) : CollectFactsM Unit := g.withContext do
  let ctx ← getLCtx
  for ldecl in ctx do
    if ldecl.isImplementationDetail then
      continue
    let ⟨0, type, expr⟩ := ← inferTypeQ ldecl.toExpr | continue
    match type with
    | ~q(@Eq.{1} $α $x $y) =>
      if (← synthInstance? (q(LE $α))).isSome then
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .eq xIdx yIdx expr
    | ~q(@LE.le $α $inst $x $y) =>
      let xIdx := ← addAtom α x
      let yIdx := ← addAtom α y
      addFact α <| .le xIdx yIdx expr
    | ~q(@LT.lt $α $inst $x $y) =>
      let xIdx := ← addAtom α x
      let yIdx := ← addAtom α y
      addFact α <| .lt xIdx yIdx expr
    | ~q(@Ne.{1} $α $x $y) =>
      if (← synthInstance? (q(LE $α))).isSome then
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .ne xIdx yIdx expr
    | ~q(Not $p) =>
      match p with
      | ~q(@LE.le $α $inst $x $y) =>
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .nle xIdx yIdx expr
      | ~q(@LT.lt $α $inst $x $y) =>
        let xIdx := ← addAtom α x
        let yIdx := ← addAtom α y
        addFact α <| .nlt xIdx yIdx expr

-- TODO: Split conjunctions.
-- TODO: Add an option for splitting disjunctions and implications.
/-- Collects facts from the local context. For each occurring type `α`, the returned map contains
a pair `(idxToAtom, facts)`, where the map `idxToAtom` converts indices to found
atomic expressions of type `α`, and `facts` contains all collected `AtomicFact`s about them. -/
def collectFacts (g : MVarId) :
    MetaM <| Std.HashMap Expr <| Std.HashMap Nat Expr × Array AtomicFact := g.withContext do
  let res := (← (collectFactsImp g).run Std.HashMap.empty).snd
  return res.map fun _ (atomToIdx, facts) =>
    let idxToAtom : Std.HashMap Nat Expr := atomToIdx.fold (init := .empty) fun acc key value =>
      acc.insert value key
    (idxToAtom, facts)

section Preprocessing

private lemma not_lt_of_not_le {α : Type} [Preorder α] {x y : α} (h : ¬(x ≤ y)) : ¬(x < y) :=
  (h ·.le)

private lemma le_of_not_lt_le {α : Type} [Preorder α] {x y : α} (h1 : ¬(x < y)) (h2 : x ≤ y) :
    y ≤ x := by
  rw [not_lt_iff_not_le_or_ge] at h1
  rcases h1 with (h1 | h1)
  · exact False.elim (h1 h2)
  · assumption

/-- Preprocesses facts for preorders. Replaces `x < y` with two equivalent facts: `x ≤ y` and
`¬ (y ≤ x)`. Replaces `x = y` with `x ≤ y`, `y ≤ x` and removes `x ≠ y`. -/
def preprocessFactsPreorder (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_lt #[proof])
      res := res.push <| .nle rhs lhs (← mkAppM ``not_le_of_lt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | .ne _ _ _ =>
      continue
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for partial orders. Replaces `x < y`, `¬ (x ≤ y)`, and `x = y` with
equivalent facts involving only `≤`, `≠`, and `≮`. -/
def preprocessFactsPartial (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``LT.lt.ne #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``LT.lt.le #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .nlt lhs rhs (← mkAppM ``not_lt_of_not_le #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | _ =>
      res := res.push fact
  return res

/-- Preprocesses facts for linear orders. Replaces `x < y`, `¬ (x ≤ y)`, `¬ (x < y)`, and `x = y`
with equivalent facts involving only `≤` and `≠`. -/
def preprocessFactsLinear (g : MVarId) (facts : Array AtomicFact) :
    MetaM <| Array AtomicFact := g.withContext do
  let mut res : Array AtomicFact := #[]
  for fact in facts do
    match fact with
    | .lt lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``LT.lt.ne #[proof])
      res := res.push <| .le lhs rhs (← mkAppM ``LT.lt.le #[proof])
    | .nle lhs rhs proof =>
      res := res.push <| .ne lhs rhs (← mkAppM ``ne_of_not_le #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_le #[proof])
    | .nlt lhs rhs proof =>
      res := res.push <| .le rhs lhs (← mkAppM ``le_of_not_lt #[proof])
    | .eq lhs rhs proof =>
      res := res.push <| .le lhs rhs (← mkAppM ``le_of_eq #[proof])
      res := res.push <| .le rhs lhs (← mkAppM ``ge_of_eq #[proof])
    | _ =>
      res := res.push fact
  return res

end Preprocessing

structure Edge where
  src : Nat
  dst : Nat
  proof : Expr

instance : ToString Edge where
  toString e := s!"{e.src} ⟶ {e.dst}"

/-- TODO -/
abbrev Graph := Array (Array Edge)

def Graph.addEdge (g : Graph) (edge : Edge) : Graph :=
  g.modify edge.src fun edges => edges.push edge

/-- Constructs a directed `Graph` using only `≤` facts. -/
def constructLeGraph (nVertexes : Nat) (facts : Array AtomicFact) (idxToAtom : Std.HashMap Nat Expr) :
    MetaM Graph := do
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

/-- Finds a contradictory `≠`-fact whose `.lhs` and `.rhs` belong to the same strongly connected
component in the `≤`-graph, implying they must be equal. -/
def findContradictoryNe (graph : Graph) (facts : Array AtomicFact) : Option AtomicFact :=
  let condensation := condense graph
  facts.find? fun fact =>
    if let .ne lhs rhs _ := fact then
      condensation[lhs]! == condensation[rhs]!
    else
      false

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
def buildTransitiveLeProof (g : Graph) (s t : Nat) (tExpr : Expr) : MetaM (Option Expr) := do
  let state : DFSState := ⟨mkArray g.size false⟩
  (buildTransitiveLeProofDFS g s t tExpr).run' state

/-- Using `≮`-facts and the `le_of_not_lt_le` lemma, add edges to the `≤`-graph `g` as long as
it remains possible. -/
def updateGraphWithNlt (g : Graph) (idxToAtom : Std.HashMap Nat Expr) (facts : Array AtomicFact) :
    MetaM Graph := do
  let nltFacts := facts.filter fun fact => match fact with | .nlt _ _ _ => true | _ => false
  let mut used : Array Bool := mkArray nltFacts.size false
  let mut g := g
  while true do
    let mut changed : Bool := false
    for i in [:nltFacts.size] do
      if used[i]! then
        continue
      let .nlt lhs rhs proof := nltFacts[i]! | throwError "Bug: Non-nlt fact in nltFacts."
      let .some pf ← buildTransitiveLeProof g lhs rhs (idxToAtom.get! rhs) | continue
      changed := true
      used := used.set! i true
      g := g.addEdge ⟨rhs, lhs, ← mkAppM ``le_of_not_lt_le #[proof, pf]⟩
    if !changed then
      break
  return g

/-- Using the `≤`-graph `g`, find a contradiction with some `≰`-fact. -/
def findContradictionWithNle (g : Graph) (idxToAtom : Std.HashMap ℕ Expr)
    (facts : Array AtomicFact) : MetaM <| Option Expr := do
  for fact in facts do
    if let .nle lhs rhs proof := fact then
      let .some pf ← buildTransitiveLeProof g lhs rhs (idxToAtom.get! rhs) | continue
      return .some <| mkApp proof pf
  return .none

/-- Supported order types: linear, partial, and preorder. -/
inductive OrderType
| lin | part | pre
deriving BEq

/-- Find the "best" instance of an order on a given type. A linear order is preferred over a partial
order, and a partial order is preferred over a preorder. -/
def findBestInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return .some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return .some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return .some .pre
  return .none

/-- A finishing tactic for solving goals in arbitrary `Preorder`, `PartialOrder`,
or `LinearOrder`. -/
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
    let mut graph ← constructLeGraph idxToAtom.size facts idxToAtom
    if orderType != .lin then
      graph ← updateGraphWithNlt graph idxToAtom facts
    if orderType == .pre then
      let .some pf ← findContradictionWithNle graph idxToAtom facts | continue
      g.assign pf
      return
    else
      let .some contNe := findContradictoryNe graph facts | continue
      let .ne lhs rhs neProof := contNe | throwError "Bug: Non-ne fact in findContradictoryNe."
      let .some pf1 ← buildTransitiveLeProof graph lhs rhs (idxToAtom.get! rhs)
        | throwError "Bug: Cannot find path in strongly connected component"
      let .some pf2 ← buildTransitiveLeProof graph rhs lhs (idxToAtom.get! lhs)
        | throwError "Bug: Cannot find path in strongly connected component"
      let pf3 ← mkAppM ``le_antisymm #[pf1, pf2]
      g.assign <| mkApp neProof pf3
      return
  throwError "No contradiction found"

end Mathlib.Tactic.Order
