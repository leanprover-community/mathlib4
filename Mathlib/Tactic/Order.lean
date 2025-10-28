/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Order.CollectFacts
import Mathlib.Tactic.Order.Preprocessing
import Mathlib.Tactic.Order.Graph.Basic
import Mathlib.Tactic.Order.Graph.Tarjan
import Mathlib.Util.ElabWithoutMVars

/-!
# `order` tactic

This module defines the `order` tactic, a decision procedure for the theories of `Preorder`,
`PartialOrder`, `LinearOrder`, and `Lattice`. It also supports `⊤` and `⊥`.

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

### Lattice
The algorithm for lattices is similar to that for partial orders, with two differences:
1. During the preprocessing step, we add the facts `x ≤ x ⊔ y` and `y ≤ x ⊔ y` if `x ⊔ y` is present
in the context, and similarly for `⊓`.
2. In step 5, we expand the `≤`-graph using the following procedure: if a vertex `v` is reachable
from both `x` and `y`, and `x ⊔ y` is present in the set of atoms, we add the edge `(x ⊔ y, v)`
using `sup_le`, and similarly for `⊓`.

One can show that this algorithm also serves as a decision procedure for the theory of lattices.

### `⊤` and `⊥`
For `⊤` and `⊥`, we add the edges `(x, ⊤)` and `(⊥, x)` for all vertices `x`, using `le_top`
and `bot_le`, respectively.
-/

namespace Mathlib.Tactic.Order

open Lean Qq Elab Meta Tactic

initialize registerTraceClass `order

/-- Finds a contradictory `≠`-fact whose `.lhs` and `.rhs` belong to the same strongly connected
component in the `≤`-graph, implying they must be equal, and then uses it to derive `False`. -/
def findContradictionWithNe (graph : Graph) (idxToAtom : Std.HashMap Nat Expr)
    (facts : Array AtomicFact) : MetaM <| Option Expr := do
  let scc := graph.findSCCs
  for fact in facts do
    let .ne lhs rhs neProof := fact | continue
    if scc[lhs]! != scc[rhs]! then
      continue
    let some pf1 ← graph.buildTransitiveLeProof idxToAtom lhs rhs
      | panic! "Cannot find path in strongly connected component"
    let some pf2 ← graph.buildTransitiveLeProof idxToAtom rhs lhs
      | panic! "Cannot find path in strongly connected component"
    let pf3 ← mkAppM ``le_antisymm #[pf1, pf2]
    return some <| mkApp neProof pf3
  return none

/-- Using the `≤`-graph `g`, find a contradiction with some `≰`-fact. -/
def findContradictionWithNle (g : Graph) (idxToAtom : Std.HashMap ℕ Expr)
    (facts : Array AtomicFact) : MetaM <| Option Expr := do
  for fact in facts do
    if let .nle lhs rhs proof := fact then
      let some pf ← g.buildTransitiveLeProof idxToAtom lhs rhs | continue
      return some <| mkApp proof pf
  return none

/-- Adds edges to the `≤`-graph using two types of facts:
1. Each fact `¬ (x < y)` allows to add the edge `(x, y)` when `y` is reachable from `x` in the
graph.
2. Each fact `x ⊔ y = z` allows to add the edge `(z, s)` when `s` is reachable from both `x`
and `y`.

We repeat the process until no more edges can be added. -/
def updateGraphWithNltInfSup (g : Graph) (idxToAtom : Std.HashMap Nat Expr)
    (facts : Array AtomicFact) : MetaM Graph := do
  let nltFacts := facts.filter fun fact => fact matches .nlt ..
  let mut usedNltFacts : Vector Bool _ := .replicate nltFacts.size false
  let infSupFacts := facts.filter fun fact => fact matches .isInf .. | .isSup ..
  let mut g := g
  repeat do
    let mut changed : Bool := false
    for h : i in [:nltFacts.size] do
      if usedNltFacts[i] then
        continue
      let .nlt lhs rhs proof := nltFacts[i] | panic! "Non-nlt fact in nltFacts."
      let some pf ← g.buildTransitiveLeProof idxToAtom lhs rhs | continue
      g := g.addEdge ⟨rhs, lhs, ← mkAppM ``le_of_not_lt_le #[proof, pf]⟩
      changed := true
      usedNltFacts := usedNltFacts.set i true
    for fact in infSupFacts do
      for idx in [:g.size] do
        match fact with
        | .isSup lhs rhs sup =>
          let some pf1 ← g.buildTransitiveLeProof idxToAtom lhs idx | continue
          let some pf2 ← g.buildTransitiveLeProof idxToAtom rhs idx | continue
          if (← g.buildTransitiveLeProof idxToAtom sup idx).isNone then
            g := g.addEdge ⟨sup, idx, ← mkAppM ``sup_le #[pf1, pf2]⟩
            changed := true
        | .isInf lhs rhs inf =>
          let some pf1 ← g.buildTransitiveLeProof idxToAtom idx lhs | continue
          let some pf2 ← g.buildTransitiveLeProof idxToAtom idx rhs | continue
          if (← g.buildTransitiveLeProof idxToAtom idx inf).isNone then
            g := g.addEdge ⟨idx, inf, ← mkAppM ``le_inf #[pf1, pf2]⟩
            changed := true
        | _ => panic! "Non-isInf or isSup fact in infSupFacts."
    if !changed then
      break
  return g

/-- Supported order types: linear, partial, and preorder. -/
inductive OrderType
| lin | part | pre
deriving BEq

instance : ToString OrderType where
  toString
  | .lin => "linear order"
  | .part => "partial order"
  | .pre => "preorder"

/-- Find the "best" instance of an order on a given type. A linear order is preferred over a partial
order, and a partial order is preferred over a preorder. -/
def findBestOrderInstance (type : Expr) : MetaM <| Option OrderType := do
  if (← synthInstance? (← mkAppM ``LinearOrder #[type])).isSome then
    return some .lin
  if (← synthInstance? (← mkAppM ``PartialOrder #[type])).isSome then
    return some .part
  if (← synthInstance? (← mkAppM ``Preorder #[type])).isSome then
    return some .pre
  return none

/-- Necessary for tracing below. -/
local instance : Ord (Nat × Expr) where
  compare x y := compare x.1 y.1

/-- Core of the `order` tactic. -/
def orderCore (only? : Bool) (hyps : Array Expr) (negGoal : Expr) (g : MVarId) : MetaM Unit := do
  g.withContext do
    let TypeToAtoms ← collectFacts only? hyps negGoal
    for (type, (idxToAtom, facts)) in TypeToAtoms do
      let some orderType ← findBestOrderInstance type | continue
      let facts : Array AtomicFact ← match orderType with
      | .pre => preprocessFactsPreorder facts
      | .part => preprocessFactsPartial facts idxToAtom
      | .lin => preprocessFactsLinear facts idxToAtom
      trace[order] "Working on type {← ppExpr type} ({orderType})"
      let atomsMsg := String.intercalate "\n" <| Array.toList <|
        ← idxToAtom.toArray.sortDedup.mapM
          fun ⟨idx, atom⟩ => do return s!"#{idx} := {← ppExpr atom}"
      trace[order] "Collected atoms:\n{atomsMsg}"
      let factsMsg := String.intercalate "\n" (facts.map toString).toList
      trace[order] "Collected facts:\n{factsMsg}"
      let mut graph ← Graph.constructLeGraph idxToAtom.size facts idxToAtom
      graph ← updateGraphWithNltInfSup graph idxToAtom facts
      if orderType == .pre then
        let some pf ← findContradictionWithNle graph idxToAtom facts | continue
        g.assign pf
        return
      else
        let some pf ← findContradictionWithNe graph idxToAtom facts | continue
        g.assign pf
        return
    throwError ("No contradiction found.\n\n" ++
      "Additional diagnostic information may be available using " ++
      "the `set_option trace.order true` command.")

/-- Args for the `order` tactic. -/
syntax orderArgs := (&" only")? (" [" term,* "]")?

/-- `order_core` is the part of the `order` tactic that tries to find a contradiction. -/
syntax (name := order_core) "order_core" orderArgs ident : tactic

open Syntax in
elab_rules : tactic
  | `(tactic| order_core $[only%$o]? $[[$args,*]]? $order_neg_goal) => withMainContext do
    let negGoal ← elabTerm order_neg_goal none
    let args ← ((args.map (TSepArray.getElems)).getD {}).mapM (elabTermWithoutNewMVars `order)
    commitIfNoEx do liftMetaFinishingTactic <| orderCore o.isSome args negGoal

/-- A finishing tactic for solving goals in arbitrary `Preorder`, `PartialOrder`,
or `LinearOrder`. Supports `⊤`, `⊥`, and lattice operations. -/
macro "order" args:orderArgs : tactic => `(tactic|
  · intros
    by_contra! _order_neg_goal
    order_core $args _order_neg_goal
)

end Mathlib.Tactic.Order
