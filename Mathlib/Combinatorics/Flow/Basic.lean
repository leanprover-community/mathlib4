/-
Copyright (c) 2024 Niklas Mohrin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niklas Mohrin
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Network Flows

In this file we introduce network flows. A flow network can be seen as a directed graph where each
arc of the graph has a fixed capacity. A flow from a source vertex $s$ to a sink vertex $t$ is an
assignment of "flow units" to each edge, such that for all vertices other than the source and the
sink, the incoming flow must equal the outgoing flow (_flow conservation_). The value of such an
assignment is the amount of flow units leaving the source $s$ and arriving at the sink $t$. In
practice, we are usually interested in finding a flow of maximal value for a given network.

## Main definitions

- `Network`: A flow network assigning capacities to all pairs of vertices. Notably, capacities and
             non-negative and the capacity from a vertex to itself is zero.
- `Network.Problem`: A `Network` along with fixed source and sink vertices $s$ and $t$.
- `Flow`: A valid assignment of flow values for a given `Network.Problem`.

## Notation

For flows `F F' : Flow Pr`, we define two relations:

 - `F ≤ F'`: Equivalent to `F.value ≤ F'.value`.
 - `F ⊆ F'`: Equivalent to `F.f ≤ F'.f`.

## References

See [goldberg_network_1989] for a thorough introduction to the topic.

## Tags

flow, network, max-flow, maxflow, cut, min-cut, mincut, graph, subflow
-/

universe u_V u_R

open BigOperators

section NetworkDefinition

variable (V : Type u_V) (R : Type u_R) [Zero R] [LE R]

/-- A flow network assigning non-negative capacities to all pairs of vertices. -/
structure Network where
  /-- The assigned capacities. -/
  cap : V → V → R
  nonneg : ∀ u v, 0 ≤ cap u v
  loopless: ∀ v, cap v v = 0

/-- A `Network` where all capacities are symmetrical. -/
structure UndirectedNetwork extends Network V R where
  symm : ∀ u v, cap u v = cap v u

end NetworkDefinition

variable {V : Type u_V} {R : Type u_R}

namespace UndirectedNetwork

/-- The graph made of all edges that have positive capacity in the network. -/
def asSimpleGraph [Zero R] [Preorder R] (N : UndirectedNetwork V R) : SimpleGraph V where
  Adj u v := 0 < N.cap u v
  symm u v huv := by simp only [N.symm, huv]
  loopless v hv := hv.ne.symm <| N.loopless v

end UndirectedNetwork

/-- A fixed choice of _source_ and _sink_ vertices $s$ and $t$ in a given `Network`. -/
structure Network.Problem [Zero R] [LE R] (N : Network V R) where
  /-- The source vertex. -/
  s : V
  /-- The sink vertex. -/
  t : V

variable [Fintype V]

section FlowDefinition

/-- The incoming flow of a vertex. --/
def flowIn [AddCommMonoid R] (f : V → V → R) (v : V) := ∑ u, f u v
/-- The outgoing flow of a vertex. --/
def flowOut [AddCommMonoid R] (f : V → V → R) (v : V) := ∑ w, f v w
/-- The excess flow of a vertex (the incoming flow minus the outgoing flow). --/
def excess [SubtractionCommMonoid R] (f : V → V → R) (v : V) := flowIn f v - flowOut f v

variable [OrderedAddCommMonoid R] {N : Network V R}

/-- A valid assignment of flow units to all edges for a given `Network.Problem`.

    Note that this definition, in contrast to what can sometimes be found in the literature, does
    not require that $f(u, v) = -f(v, u)$. This extra requirement eliminates cycles between two
    vertices and makes some theorem statements shorter. However, since larger cycles are still
    permitted, this usually does not help in proofs. To the contrary, defining a flow becomes more
    cumbersome, sometimes significantly so. -/
@[ext]
structure Flow (Pr : N.Problem) where
  /-- The assignment of flow units to each edge. -/
  f : V → V → R
  nonneg : ∀ u v, 0 ≤ f u v
  conservation : ∀ v, v ≠ Pr.s ∧ v ≠ Pr.t → flowOut f v = flowIn f v
  capacity : ∀ u v, f u v ≤ N.cap u v

/-- The flow, which assigns zero to all edges. -/
def Network.Problem.nullFlow (Pr : N.Problem) : Flow Pr where
  f _ _ := 0
  nonneg _ _ := le_rfl
  conservation _ _ := rfl
  capacity := N.nonneg

instance {Pr : N.Problem} : Zero (Flow Pr) where
  zero := Pr.nullFlow

end FlowDefinition

namespace Flow
section FlowValue

variable [OrderedAddCommGroup R] {N : Network V R} {Pr : N.Problem}

/-- The value of a flow is the amount of flow units that leave the source vertex and arrive at the
    sink vertex. In particular, this is equal to the outgoing flow of the source that does not
    return to it again. -/
def value (F : Flow Pr) := flowOut F.f Pr.s - flowIn F.f Pr.s

@[simp]
instance : Preorder (Flow Pr) := Preorder.lift Flow.value

instance [IsTotal R LE.le] : IsTotalPreorder (Flow Pr) LE.le where
  total F F' := by simp only [instPreorder, Preorder.lift, total_of]

end FlowValue

section Subflows

variable [OrderedAddCommGroup R] {N : Network V R} {Pr : N.Problem}

@[simp]
instance : HasSubset (Flow Pr) where
  Subset F₁ F₂ := F₁.f ≤ F₂.f

instance : IsPartialOrder (Flow Pr) (· ⊆ ·) where
  refl F := by simp only [instHasSubset, le_refl]
  trans F₁ F₂ F₃ h₁₂ h₂₃ := by simp_all only [instHasSubset, le_trans h₁₂ h₂₃]
  antisymm F₁ F₂ h₁₂ h₂₁ := by ext u v; exact le_antisymm (h₁₂ u v) (h₂₁ u v)

@[simp]
instance : HasSSubset (Flow Pr) where
  SSubset F₁ F₂ := F₁.f < F₂.f

instance : IsStrictOrder (Flow Pr) (· ⊂ ·) where
  irrefl F := by simp only [instHasSSubset, lt_self_iff_false, not_false_eq_true, forall_const]
  trans F₁ F₂ F₃ h₁₂ h₂₃ := by simp_all only [instHasSSubset, lt_trans h₁₂ h₂₃]

instance : IsNonstrictStrictOrder (Flow Pr) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left F₁ F₂ := by
    constructor <;> (intro h; simp_all only [instHasSSubset, instHasSubset]; exact h)

end Subflows
end Flow
