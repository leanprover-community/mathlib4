/-
Copyright (c) 2024 Niklas Mohrin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niklas Mohrin
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Combinatorics.Digraph.Basic

/-!
# Network Flows

In this file we introduce network flows. A flow network can be seen as a directed graph where each
arc of the graph has a fixed capacity. A flow from a source vertex `s` to a sink vertex `t` is an
assignment of "flow units" to each edge, such that for all vertices other than the source and the
sink, the incoming flow must equal the outgoing flow (_flow conservation_). The value of such an
assignment is the amount of flow units leaving the source `s` and arriving at the sink `t`. In
practice, we are usually interested in finding a flow of maximal value for a given network.

## Main definitions

- `Network`: A flow network assigning capacities to all pairs of vertices. Notably, capacities and
             non-negative and the capacity from a vertex to itself is zero.
- `PseudoFlow`, `PreFlow`, and `Flow`: An assignment of flow values for a given `Network`, abiding
                                       increasingly strict constraints.

## Notation

For flows `f f' : N.PseudoFlow`, we define `f ≤ f'` as the _subflow relation_, indicating that for
all `u v : V`, `f u v ≤ f' u v`.

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
structure Network extends Digraph V where
  Adj _ _ := True
  /-- The assigned capacities. -/
  cap : V → V → R
  nonneg : ∀ u v, 0 ≤ cap u v
  cap_zero_of_not_adj : ∀ u v, ¬Adj u v → cap u v = 0 := by intro u v; aesop

/-- A `Network` where all capacities are symmetrical. -/
structure UndirectedNetwork extends Network V R where
  symm : ∀ u v, cap u v = cap v u

end NetworkDefinition

variable {V : Type u_V} {R : Type u_R}

namespace Network

section PseudoFlowDefinition

variable [Zero R] [Preorder R]

/-- A `PseudoFlow` is an assignment of non-negative flow values to each arc of the network, such
that the assigned amount does not exceed the capacity.

Note that this definition, in contrast to what can sometimes be found in the literature, does
not require that $f(u, v) = -f(v, u)$. This extra requirement eliminates cycles between two
vertices and makes some theorem statements shorter. However, since larger cycles are still
permitted, this usually does not help in proofs. To the contrary, defining a flow becomes more
cumbersome, sometimes significantly so. -/
@[ext]
structure PseudoFlow (N : Network V R) where
  /-- The assignment of flow values to each arc.
  Do NOT use. Use the coercion to function instead. -/
  toFun : V → V → R
  nonneg' : ∀ u v, 0 ≤ toFun u v
  capacity' : ∀ u v, toFun u v ≤ N.cap u v

namespace PseudoFlow

variable {N : Network V R}

instance instFunLike : FunLike N.PseudoFlow V (V → R) where
  coe := PseudoFlow.toFun
  coe_injective' f g h := by cases f; cases g; congr

variable (f : N.PseudoFlow)

lemma nonneg : ∀ u v, 0 ≤ f u v := f.nonneg'

lemma capacity : ∀ u v, f u v ≤ N.cap u v := f.capacity'

instance : Zero N.PseudoFlow where
  zero.toFun _ _ := 0
  zero.nonneg' _ _ := le_rfl
  zero.capacity' := N.nonneg

end PseudoFlow
end PseudoFlowDefinition

variable [Fintype V]

namespace PseudoFlow

variable [Preorder R] [AddCommMonoid R] {N : Network V R} (f : N.PseudoFlow) (v : V)

/-- The incoming flow of a vertex. --/
def incoming := ∑ u, f u v
/-- The outgoing flow of a vertex. --/
def outgoing := ∑ w, f v w
/-- The excess flow of a vertex (the incoming flow minus the outgoing flow). --/
def excess [Sub R] := f.incoming v - f.outgoing v

end PseudoFlow

section PreFlowDefinition

variable [Preorder R] [AddCommMonoid R] (N : Network V R) (s t : V)

/-- A `PreFlow` from `s` to `t` is a `PseudoFlow` such that all vertices except `s` and `t` have
non-negative excess, that is, the outgoing flow is at most as much as the incoming flow. -/
@[ext]
structure PreFlow extends N.PseudoFlow where
  excess_nonneg : ∀ v, v ≠ s → v ≠ t → toPseudoFlow.outgoing v ≤ toPseudoFlow.incoming v

namespace PreFlow

variable {N s t}

instance : Zero (N.PreFlow s t) where
  zero := { (0 : N.PseudoFlow) with excess_nonneg := fun _ _ _ ↦ le_rfl }

/-- The value of a flow is the amount of flow units that leave the source vertex and arrive at the
sink vertex. In particular, this is equal to the excess of `t`. -/
def value [Sub R] (f : N.PreFlow s t) := f.excess t

end PreFlow
end PreFlowDefinition

section FlowDefinition

variable [Preorder R] [AddCommMonoid R] (N : Network V R) (s t : V)

/-- A `Flow` from `s` to `t` is a `PreFlow s t`, but instead of requiring non-negative excess, it
requires that the excess is 0 (also called _flow conservation_). -/
@[ext]
structure Flow extends N.PreFlow s t where
  conservation : ∀ v, v ≠ s → v ≠ t → toPseudoFlow.outgoing v = toPseudoFlow.incoming v
  excess_nonneg v hs ht := (conservation v hs ht).le

namespace Flow

instance : Zero (N.Flow s t) where
  zero := { (0 : N.PreFlow s t) with conservation := fun _ _ _ ↦ rfl }

end Flow
end FlowDefinition

section SummingLemmas
variable [Preorder R] [AddCommGroup R] {N : Network V R}

namespace PseudoFlow

variable (f : N.PseudoFlow)

lemma sum_outgoing_eq_sum_incoming : ∑ v, f.outgoing v = ∑ v, f.incoming v := by
  unfold outgoing incoming
  rw [Finset.sum_comm]

@[simp]
lemma sum_excess_zero : ∑ v, f.excess v = 0 := by simp [excess, sum_outgoing_eq_sum_incoming]

end PseudoFlow

namespace Flow

variable {s t : V} (f : N.Flow s t)

lemma excess_source_zero_of_eq (hst : s = t) : f.excess s = 0 := by
  rw [← f.sum_excess_zero]
  apply Eq.symm
  apply Finset.sum_eq_single_of_mem s (Finset.mem_univ _)
  intro v _ hs
  simp [PseudoFlow.excess, f.conservation v hs (hst ▸ hs)]

lemma value_zero_of_eq (hst : s = t) : f.value = 0 := by
  subst t
  rw [PreFlow.value, f.excess_source_zero_of_eq rfl]

lemma excess_source_eq_neg_excess_sink : f.excess s = -f.excess t := by
  wlog hst : s ≠ t
  · rw [not_not] at hst
    subst t
    simp [f.excess_source_zero_of_eq]
  apply eq_neg_of_add_eq_zero_left
  rw [← f.sum_excess_zero]
  apply Eq.symm
  apply Finset.sum_eq_add_of_mem s t (Finset.mem_univ _) (Finset.mem_univ _) hst
  intro v _ hv
  simp [PseudoFlow.excess, f.conservation v hv.left hv.right]

lemma excess_sink_eq_neg_excess_source : f.excess t = -f.excess s := by
  rw [excess_source_eq_neg_excess_sink, neg_neg]

lemma value_eq_outgoing_minus_incoming_source : f.value = f.outgoing s - f.incoming s := by
  rw [PreFlow.value, excess_sink_eq_neg_excess_source, PseudoFlow.excess, neg_sub]

end Flow
end SummingLemmas

section Subflows
namespace PseudoFlow

variable [PartialOrder R] [AddCommGroup R] {N : Network V R}

@[simp]
instance : PartialOrder (N.PseudoFlow) := PartialOrder.lift toFun instFunLike.coe_injective'

instance : OrderBot (N.PseudoFlow) where
  bot := 0
  bot_le := nonneg

end PseudoFlow
end Subflows
end Network
