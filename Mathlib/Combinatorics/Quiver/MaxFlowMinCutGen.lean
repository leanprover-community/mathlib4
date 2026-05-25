/-
Copyright (c) 2026 "ADD NAMES". All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: "ADD NAMES"
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Init.Data.List.BasicAux
import Mathlib.Data.List.Intervals
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Finset
open scoped BigOperators

-- ============================================================
-- STRUCTURES
-- ============================================================

/-- Given a set of vertices, we designate s to be the source and t to be the sink. -/
structure STVertices (V : Type*) [Fintype V] where
  s : V
  t : V
  source_not_sink : s ≠ t

/-- Given the source and the sink, we define a flow network as something that assigns a
  nonnegative capacity to each edge of the complete graph, where 0 is implicitly used for
  missing edges. -/
structure FlowNetwork (V α : Type*) [Fintype V] [Ring α] [LinearOrder α] extends STVertices V where
  c : V → V → α
  nonneg_capacity : ∀ u v : V, c u v ≥ 0

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going into S -/
noncomputable
def incoming_cut_f {V α : Type*} [Fintype V] [Ring α]
    (f : V → V → α) (S : Finset V) : α :=
  ∑ x ∈ Finset.univ \ S, ∑ y ∈ S, f x y

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going out of S -/
noncomputable
def outgoing_cut_f {V α : Type*} [Fintype V] [Ring α]
    (f : V → V → α) (S : Finset V) : α :=
  ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, f x y

/-- A relaxedFlow is defined on a complete graph with source and sink and assigns to each edge
  a nonnegative flow value that satisfies flow conservation and does not send flow into the
  source or out of the sink. -/
structure RelaxedFlow {V : Type*} (α : Type*) [Fintype V] [Ring α] [LinearOrder α]
    (G : STVertices V) where
  f : V → V → α
  nonneg_flow : ∀ u v : V, f u v ≥ 0
  conservation : ∀ v : V, v ≠ G.s → v ≠ G.t → outgoing_cut_f f {v} = incoming_cut_f f {v}
  no_edges_in_source : ∀ u : V, f u G.s = 0
  no_edges_out_sink : ∀ u : V, f G.t u = 0

open Classical in
/-- An S-T cut partitions the set of vertices into a set S that
 contains the source and a set T that contains the sink. -/
structure Cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : FlowNetwork V α) where
  S : Finset V
  T : Finset V
  hT : T = univ \ S
  sins : G.s ∈ S
  tint : G.t ∈ T

-- ============================================================
-- FLOWS
-- ============================================================

/-- A ValidFlow is a relaxedFlow that also satisfies capacity constraints which are
  defined in a FlowNetwork. -/
def ValidFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : FlowNetwork V α)
    (g : RelaxedFlow α G.toSTVertices) : Prop :=
  ∀ u v : V, g.f u v ≤ G.c u v

/-- An (explicit) equivalent definition for flow conservation. -/
lemma conservation_eq {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : STVertices V)
    (flow : RelaxedFlow α G) : ∀ v : V, v ≠ G.s → v ≠ G.t → ∑ x, (flow.f x v - flow.f v x) = 0 := by
  intro v vns vnt
  have : outgoing_cut_f flow.f {v} = incoming_cut_f flow.f {v} := flow.conservation v vns vnt
  unfold incoming_cut_f outgoing_cut_f at this
  simp at this
  simp [this]

/-- The addition/augmentation of a flow with another. Implicitly cancels out any 2-cycles,
  guaranteeing that flow cannot move between two vertices in both directions. This is
  necessary to guarantee augmenting a valid flow from the original network with the residual
  network results in a valid flow in the original network. -/
def augment {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : STVertices V} : RelaxedFlow α G → RelaxedFlow α G → RelaxedFlow α G :=
  fun g h => {
    f u v := max (g.f u v + h.f u v - g.f v u - h.f v u) 0
    nonneg_flow := by simp
    conservation := by
      intro v vns vnt
      simp only [outgoing_cut_f, subset_univ, sum_sdiff_eq_sub, sum_singleton, sum_sub_distrib,
        add_sub_cancel_left, sub_self, max_self, sub_zero, incoming_cut_f]
      have h₁: ∑ x, (max (g.f x v + h.f x v - g.f v x - h.f v x) 0
        - max (-(g.f x v + h.f x v - g.f v x - h.f v x)) 0) = 0 := by
        simp only [max_zero_sub_max_neg_zero_eq_self (g.f _ v + h.f _ v - g.f v _ - h.f v _)]
        calc
          ∑ x, (g.f x v + h.f x v - g.f v x - h.f v x)
          = ∑ x, (g.f x v - g.f v x) + ∑ x, (h.f x v - h.f v x) := by
            simp [Finset.sum_add_distrib]; grind
          _ = 0 := by
            simp only [add_eq_right, conservation_eq G g v vns vnt,
              conservation_eq G h v vns vnt];
      symm
      rw [←sub_eq_zero]
      have : ∀ x, -(g.f x v + h.f x v - g.f v x - h.f v x)
        = (g.f v x + h.f v x - g.f x v - h.f x v) := by
          intro x; grind
      simp only [this, sum_sub_distrib] at h₁
      exact h₁
    no_edges_in_source := by
      intro u;
      simp [g.no_edges_in_source, h.no_edges_in_source];
      grind [g.nonneg_flow G.s u, h.nonneg_flow G.s u]
    no_edges_out_sink := by
      intro u; simp [g.no_edges_out_sink, h.no_edges_out_sink];
      grind [g.nonneg_flow u G.t, h.nonneg_flow u G.t]
    }

infixl:70 " ⋄ "   => augment

lemma augment_comm {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : STVertices V} : ∀ F F' : RelaxedFlow α G, F ⋄ F' = F' ⋄ F := by
  intro F F'
  simp only [augment, RelaxedFlow.mk.injEq]
  grind

lemma augment_assoc {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : STVertices V} : ∀ F F' F'' : RelaxedFlow α G, (F ⋄ F') ⋄ F'' = F ⋄ (F' ⋄ F'') := by
  intro F F' F''
  simp only [augment, RelaxedFlow.mk.injEq]
  grind

/-- The value of a flow: the amount of flow going out of the sink. -/
noncomputable
def flowValue {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : STVertices V)
    (flow : RelaxedFlow α G) : α := outgoing_cut_f flow.f {G.s}

/-- The value of a flow is nonnegative. -/
lemma flow_value_nonneg {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : STVertices V) : ∀F : RelaxedFlow α G, flowValue G F ≥ 0 := by
  intro F; simp [flowValue, outgoing_cut_f, F.no_edges_in_source, sum_nonneg, F.nonneg_flow]

/-- The value of a flow is additive under augmentation. -/
lemma add_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : STVertices V) (flow₁ flow₂ : RelaxedFlow α G) :
      flowValue G (flow₁ ⋄ flow₂) = flowValue G flow₁ + flowValue G flow₂ := by
  have: ∀ x, (flow₁.f G.s x + flow₂.f G.s x) ≥ 0 := by
    intro x; grind [flow₁.nonneg_flow G.s x, flow₂.nonneg_flow G.s x]
  simp [flowValue, (· ⋄ ·), outgoing_cut_f,
   flow₁.no_edges_in_source, flow₂.no_edges_in_source, this, sum_add_distrib]

/-- The capacity of an S-T cut is the sum of edge capacities of edges going from S to T. -/
noncomputable
def cutCap {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] {G : FlowNetwork V α}
    (c : Cut G) : α := outgoing_cut_f G.c c.S

/-- The flow of an S-T cut given a RelaxedFlow is the sum of flows going over edges going
  from S to T. -/
noncomputable
def cutFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] {G : FlowNetwork V α}
    (g : RelaxedFlow α G.toSTVertices) (c : Cut G) : α := outgoing_cut_f g.f c.S

/-- A flow is maximal if it respects capacities and has the largest flow value compared to
 other flows that respect capacities. -/
def IsMaxFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] {G : FlowNetwork V α}
    (fn : RelaxedFlow α G.toSTVertices) : Prop :=
  ValidFlow G fn ∧ ∀ fn' : RelaxedFlow α G.toSTVertices, ValidFlow G fn' →
    flowValue G.toSTVertices fn' ≤ flowValue G.toSTVertices fn

/-- A cut is minimal if its capapcity is minimal. -/
def IsMinCut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : FlowNetwork V α)
    (fn : Cut G) : Prop := ∀ fn' : Cut G, cutCap fn ≤ cutCap fn'

/-- The residual network is a flow network defined using an existing flow network and flow.
  It uses the same source and sink. The capacity of an edge u v is given by its original capacity
  minus the amount of flow going over this edge plus the amount of flow going in the opposite
  direction. -/
def ResidualNetwork {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) (h : ValidFlow G F) : FlowNetwork V α
      where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c u v := G.c u v - F.f u v + F.f v u
  nonneg_capacity := by intro u v; rw [ge_iff_le]; grind [h u v, F.nonneg_flow v u]

/-- Augmenting a valid flow in the original network with a valid flow in its residual network
  results in a new valid flow. -/
lemma valid_augmentation_of_valid_residual {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G F) :
        ∀F' : (RelaxedFlow α G.toSTVertices), ValidFlow (ResidualNetwork G F h) F' →
          ∀ u v : V, (F ⋄ F').f u v ≤ G.c u v := by
  intro F' val_F' u v
  simp [(· ⋄ ·)]
  constructor
  · have : F'.f u v ≤ G.c u v - F.f u v + F.f v u := by exact val_F' u v
    grind [F'.nonneg_flow v u, F.nonneg_flow u v]
  · simp [G.nonneg_capacity u v]

/-- If a flow is maximal, all flows in its residual graph have value 0. -/
lemma no_augmenting_of_max_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : IsMaxFlow F) :
        ∀F' : (RelaxedFlow α G.toSTVertices), ValidFlow (ResidualNetwork G F h.1) F' →
          flowValue G.toSTVertices F' = 0 := by
  intro F' g
  by_contra con
  push Not at con
  have: flowValue G.toSTVertices F' > 0 := by
   apply lt_of_le_of_ne;
   · grind [flow_value_nonneg G.toSTVertices F']
   · symm; exact con
  let optF := F ⋄ F'
  have optge : flowValue G.toSTVertices optF > flowValue G.toSTVertices F := by calc
   flowValue G.toSTVertices optF = flowValue G.toSTVertices F + flowValue G.toSTVertices F' :=
   by exact add_flow G.toSTVertices F F'
   _ > flowValue G.toSTVertices F := by grind
  have optval : ValidFlow G optF := by
   apply valid_augmentation_of_valid_residual G F h.1 F' g
  have: ¬IsMaxFlow F := by
   simp only [IsMaxFlow, not_and, not_forall, not_le]; intro _; use optF;
  contradiction

-- ============================================================
-- WEAK DUALITY + OPTIMALITY CRITERION
-- ============================================================

/-- The flow of a cut is no more than the capacity of a cut. -/
lemma cut_flow_le_cut_cap {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices) (h : ValidFlow G g) :
      cutFlow g C ≤ cutCap C := by
  simp only [cutFlow, cutCap, outgoing_cut_f]
  apply sum_le_sum
  intro v _
  apply sum_le_sum
  intro w _
  exact h v w

open Classical in
/-- Flow conservation of the vertices in S without the source. -/
lemma sCut_flow_conservation {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices) :
      ∑ v ∈ C.S \ {G.s}, ∑ w : V, (g.f v w - g.f w v) = 0 := by
  apply sum_eq_zero
  intro v vinsns
  obtain ⟨l, r⟩ := Finset.mem_sdiff.mp vinsns
  have vns : v ≠ G.s := List.ne_of_not_mem_cons r
  have vnt : v ≠ G.t := by
    by_contra h
    have : v ∈ C.T := by rw [h]; exact C.tint
    have : v ∈ C.S ∩ C.T := by exact mem_inter_of_mem l this;
    have : C.S ∩ C.T ≠ ∅ := by exact ne_empty_of_mem this
    have STempty : C.S ∩ C.T = ∅ := by simp [C.hT];
    contradiction
  rw [sum_sub_distrib, ←zero_eq_neg, neg_sub, ←sum_sub_distrib,
  conservation_eq G.toSTVertices g v vns vnt]

/-- You can add a singleton value in the sum. -/
lemma sum_erase_add {V α : Type*} [DecidableEq V] [Ring α] {S : Finset V} {a : V} (h : a ∈ S)
    (f : V → α) : f a + ∑ b ∈ S \ {a}, f b = ∑ b ∈ S, f b := by
  refine add_eq_of_eq_sub ?_
  have : ∑ b ∈ S, f b - ∑ b ∈ S \ {a}, f b = f a := by simp [h]
  rw [this]

/-- If summing over a subset evaluates to 0, you can that subset from the original sum. -/
lemma sum_subset_zero_cancel {V α : Type*} [DecidableEq V] [Ring α] {S : Finset V} {T : Finset V}
    (f : V → α) (h : T ⊆ S) (h' : ∑ x ∈ T, f x = 0) : ∑ b ∈ S, f b = ∑ b ∈ S \ T, f b := by
  simp [h, h']

open Classical in
/-- For any cut, the value of a flow is equal to the sum of flows over edges from S to T
  minus the flow over edges from T to S. -/
lemma flow_value_eq_net_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices) :
      flowValue G.toSTVertices g = ∑ v ∈ C.S, ∑ w ∈ univ \ C.S, (g.f v w - g.f w v) := by
  rw [← add_zero (flowValue G.toSTVertices g), ← sCut_flow_conservation C g]
  simp only [flowValue, outgoing_cut_f]
  have hsum : ∑ x ∈ ({G.s} : Finset V), ∑ y ∈ univ \ {G.s}, g.f x y =
      ∑ x ∈ ({G.s} : Finset V), ∑ y ∈ univ \ {G.s}, (g.f x y - g.f y x) := by
    simp [g.no_edges_in_source]
  have hinner : ∑ v ∈ C.S, ∑ w ∈ C.S, (g.f w v - g.f v w) = 0 := by
    simp only [sum_sub_distrib]; rw [sum_comm]; simp
  calc
    ∑ x ∈ ({G.s} : Finset V), ∑ y ∈ univ \ {G.s}, g.f x y
        + ∑ v ∈ C.S \ {G.s}, ∑ w, (g.f v w - g.f w v)
      = ∑ x ∈ ({G.s} : Finset V), ∑ y ∈ univ \ {G.s}, (g.f x y - g.f y x)
        + ∑ v ∈ C.S \ {G.s}, ∑ w, (g.f v w - g.f w v) := by rw [hsum]
    _ = ∑ x ∈ ({G.s} : Finset V), ∑ y, (g.f x y - g.f y x)
        + ∑ v ∈ C.S \ {G.s}, ∑ w, (g.f v w - g.f w v) := by
          simp [g.no_edges_in_source]
    _ = ∑ v ∈ C.S, ∑ w, (g.f v w - g.f w v) := by
          simp only [sum_singleton]
          rw [sum_erase_add C.sins (fun v => ∑ w, (g.f v w - g.f w v))]
    _ = ∑ v ∈ C.S, ∑ w ∈ univ \ C.S, (g.f v w - g.f w v) := by
          rw [sum_comm]
          have htmp := sum_subset_zero_cancel (fun v => ∑ w ∈ C.S, (g.f w v - g.f v w))
            (subset_univ C.S) hinner
          rw [htmp, sum_comm]

/-- The value of a flow is no more than the flow of any cut. -/
lemma flow_le_cut_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices) :
    flowValue G.toSTVertices g ≤ cutFlow g C := by
  classical
  rw [flow_value_eq_net_flow C g]
  simp only [cutFlow, outgoing_cut_f]
  apply Finset.sum_le_sum; intro v _
  apply Finset.sum_le_sum; intro w _
  grind [g.nonneg_flow w v]

/-- The value of a flow is no more than the capacity of any cut. -/
theorem weak_duality {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices) (h : ValidFlow G g) :
      flowValue G.toSTVertices g ≤ cutCap C := by
  grind [cut_flow_le_cut_cap C g h, flow_le_cut_flow C g]

/-- If the value of a flow is equal to the capacity of any cut, the flow value is maximal. -/
lemma max_flow_of_flow_value_eq_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] {G : FlowNetwork V α} (C : Cut G) (g : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G g) : flowValue G.toSTVertices g = cutCap C → IsMaxFlow g := by
    intro h'
    constructor
    · exact h
    · rw [h']
      apply weak_duality

-- ===========================================================
-- TRIVIAL (ZERO) FLOWS
-- ===========================================================
/-- The trivial (zero) flow that doesn't send flow over any edge -/
def trivialFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : STVertices V) :
    RelaxedFlow α G where
  f := fun x y => 0
  nonneg_flow := by simp only [ge_iff_le, Std.le_refl, implies_true]
  conservation := by grind [outgoing_cut_f, incoming_cut_f]
  no_edges_in_source := by simp only [implies_true]
  no_edges_out_sink := by simp only [implies_true]

/-- The trivial flow doesn't send any flow over an edge -/
@[simp]
lemma zero_edge_flow_of_trivialFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    (G : STVertices V) : ∀ x y, (trivialFlow G).f x y = (0 : α) := by simp [trivialFlow]

/-- The value of the trivial flow is 0 -/
@[simp]
lemma zero_flowValue_of_trivialFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    (G : STVertices V) : flowValue G (trivialFlow G) = (0 : α) := by
  simp only [flowValue, outgoing_cut_f, zero_edge_flow_of_trivialFlow, sum_const_zero]

/-- The trivial flow is always valid -/
lemma valid_flow_of_trivialFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) : ValidFlow G (trivialFlow G.toSTVertices) := by
  simp only [ValidFlow, zero_edge_flow_of_trivialFlow, G.nonneg_capacity, implies_true]

/-- Augmenting a valid flow with the trivial flow results in a valid flow -/
lemma valid_augmentation_of_trivialFlow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (validF : ValidFlow G F) : ValidFlow G (F ⋄ (trivialFlow G.toSTVertices)) := by
  rw [ValidFlow] at validF
  simp only [ValidFlow, (· ⋄ ·), zero_edge_flow_of_trivialFlow, add_zero, sub_zero,
    sup_le_iff, tsub_le_iff_right, G.nonneg_capacity, and_true]
  intro u v
  trans G.c u v
  · exact validF u v
  · grind [F.nonneg_flow v u]

-- ============================================================
-- AUGMENTING PATHS
-- ============================================================

/-- A simple path from u to v, represented as a nodup list of vertices. -/
structure UVPath {V : Type*} [Fintype V] (u v : V) where
  verts : List V
  nonempty : verts ≠ []
  nodup : verts.Nodup
  ustart : verts.head nonempty = u
  vend : verts.getLast nonempty = v

/-- A valid path in a flow network: every consecutive pair has positive capacity. -/
structure ValidUVPath {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : FlowNetwork V α)
    (u v : V) extends UVPath u v where
  valid : ∀ (i : ℕ) (h : i < verts.length - 1), G.c (verts[i]) (verts[i+1]) > 0

/-- An augmenting path is a valid path from s to t. -/
def augmentingPath {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] (G : FlowNetwork V α) :=
  ValidUVPath G G.s G.t

/-- A path between two distinct vertices has length at least 2 -/
lemma UVPath_ge_two_of_u_ne_v {V : Type*} [Fintype V] {u v : V} (p : UVPath u v) (h : u ≠ v) :
    p.verts.length ≥ 2 := by
  grind [p.ustart, p.vend]

/-- The bottleneck capacity of a path: the minimum edge capacity along it. -/
def UVPath.bottleneck {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    (G : FlowNetwork V α) {u v : V} (p : UVPath u v) (h : u ≠ v) : α := by
  have : p.verts.length ≥ 2 := by apply UVPath_ge_two_of_u_ne_v p h
  have : p.verts.tail.length ≥ 1 := by grind
  let J := List.zipWith G.c p.verts p.verts.tail
  have : J.length ≥ 1 := by grind
  exact J.min (by grind)

/-- The bottleneck is not more than any of the capacities of edges in the path -/
lemma bottleneck_le_edge_flow {V α : Type*} [Ring α] [LinearOrder α] [Fintype V]
     (G : FlowNetwork V α) {u v : V} (p : UVPath u v) (h : u ≠ v) :
      ∀ (i : ℕ) (h' : i < p.verts.length - 1), p.bottleneck G h ≤ G.c p.verts[i] p.verts[i+1] := by
  intro i h'
  have h'' : (p.verts[i], p.verts[i + 1]) = (List.zip p.verts p.verts.tail)[i]'(by grind) :=
    by grind
  have : G.c p.verts[i] p.verts[i+1] = (List.zipWith G.c p.verts p.verts.tail)[i]'(by grind) :=
    by grind
  rw [this]
  simp only [List.getElem_zipWith, List.getElem_tail, ge_iff_le]
  let J := List.zipWith G.c p.verts p.verts.tail
  have hlen : J.length ≥ 1 := by
    grind
  have hmem : G.c p.verts[i] p.verts[i+1] ∈ J := by
    dsimp [J]
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simpa [List.length_zipWith] using h'
    · simp [List.getElem_zipWith]
  rw [UVPath.bottleneck]
  exact List.min_le_of_mem hmem

/-- Some edge in the path has capacity equal to the bottleneck -/
lemma ex_edge_flow_eq_bottleneck {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    (G : FlowNetwork V α) {u v : V} (p : UVPath u v) (h : u ≠ v) :
      ∃ (i : ℕ) (h' : i < p.verts.length - 1), p.bottleneck G h = G.c p.verts[i] p.verts[i+1] := by
  let xs := List.zipWith G.c p.verts p.verts.tail
  have : xs.length ≥ 1 := by grind [UVPath_ge_two_of_u_ne_v]
  have : xs.min (by grind) ∈ xs := by exact List.min_mem (UVPath.bottleneck._proof_3 G p this)
  use xs.idxOf (xs.min (by grind))
  have : List.idxOf (xs.min (by grind)) xs < p.verts.length - 1 := by grind
  use this
  have : UVPath.bottleneck G p h = xs.min (by grind) := by grind [UVPath.bottleneck]
  rw [this]
  let i := xs.idxOf (xs.min (by grind))
  have : xs[i]'(by grind) = xs.min (by grind) := by grind
  have : G.c p.verts[i] p.verts[i+1] = xs.min (by grind):= by grind
  grind

/-- The bottleneck of a valid path is positive. -/
lemma pos_bottleneck_of_valid {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} {u v : V} (p : ValidUVPath G u v) (h : u ≠ v) :
      p.toUVPath.bottleneck G h > 0 := by
  obtain ⟨i, ⟨h', h''⟩⟩ := ex_edge_flow_eq_bottleneck G p.toUVPath h
  grind [bottleneck_le_edge_flow G p.toUVPath h i h', p.valid i h']

/-- The flow induced by an augmenting path: send bottleneck flow along each edge of the path. -/
def pathFlow {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (p : augmentingPath G) :
      V → V → α := fun a b => if ∃ (i : ℕ) (h : i < p.verts.length - 1),
        a = p.verts[i] ∧ b = p.verts[i+1] then p.bottleneck G G.source_not_sink else 0

/-- If a list has no duplicates, then no two distinct entries of it are equal -/
lemma list_entry_neq_of_nodup {V : Type*} (l : List V) (i j : ℕ) (h₀ : i < l.length)
    (h₁ : j < l.length) (h₂ : i ≠ j) : l.Nodup → l[i] ≠ l[j] := by
  intro hnodup hEq
  apply h₂
  exact hnodup.getElem_inj_iff.mp hEq

/-- If two lookups in a list with no duplicates are equal, the lookup positions must be equal -/
lemma eq_index_if_nodup {V : Type*} (l : List V) (i j : ℕ) (h₀ : i < l.length)
    (h₁ : j < l.length) (h₂ : l[i] = l[j]) : l.Nodup → i = j := by
  intro hnodup
  exact (List.getElem_inj hnodup).mp h₂

/-- The amount of flow leaving a vertex that is contained in an augmenting path equals
  the bottleneck of the augmenting path -/
lemma augmentingPath_flow_out {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (p : augmentingPath G) (i : ℕ) (h : i < p.verts.length - 1) :
      outgoing_cut_f (pathFlow p) {p.verts[i]} = p.bottleneck G G.source_not_sink := by
  simp only [outgoing_cut_f, subset_univ, sum_sdiff_eq_sub, sum_singleton]
  have hz: ∀ v ≠ p.verts[i+1], pathFlow p p.verts[i] v = 0 := by
    intro v vnp
    rw [pathFlow]
    have : ¬ ∃ i_1, ∃ (h_1 : i_1 < p.verts.length - 1),
      p.verts[i] = p.verts[i_1] ∧ v = p.verts[i_1 + 1] := by
      push Not
      intro j hj ij
      have iltlen : i < p.verts.length := by grind
      have jltlen : j < p.verts.length := by grind
      have : j = i := eq_index_if_nodup p.verts j i jltlen iltlen (ij).symm p.nodup
      grind
    simp [this]
  have : ∑ y, pathFlow p p.verts[i] y - pathFlow p p.verts[i] p.verts[i] =
    pathFlow p p.verts[i] p.verts[i+1] := by
    have : pathFlow p p.verts[i] p.verts[i] = 0 := by
      have h₁: i < p.verts.length := by grind
      have h₂: i + 1 < p.verts.length := by grind
      have h₃ : i ≠ i+1 := by simp
      simp [hz p.verts[i] (list_entry_neq_of_nodup p.verts i (i+1) h₁ h₂ h₃ p.nodup)]
    simp only [this, sub_zero]
    have zsum : ∑ y ≠ p.verts[i+1], pathFlow p p.verts[i] y = 0 := by
      apply sum_eq_zero; grind
    have : ∑ y, pathFlow p p.verts[i] y = pathFlow p p.verts[i] p.verts[i+1] +
      ∑ y ≠ p.verts[i+1], pathFlow p p.verts[i] y := by simp
    rw [this]; simp [zsum]
  have : pathFlow p p.verts[i] p.verts[i + 1] =
    UVPath.bottleneck G p.toUVPath G.source_not_sink := by
    rw [pathFlow]
    have : ∃ j, ∃ (hv : j < p.verts.length - 1), p.verts[i] = p.verts[j] ∧
      p.verts[i + 1] = p.verts[j + 1] := by use i, h;
    simp [this]
  grind

/-- The amount of flow entering a vertex that is contained in an augmenting path equals
  the bottleneck of the augmenting path -/
lemma augmentingPath_flow_in {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (p : augmentingPath G) (i : ℕ) (h₁ : i > 0) (h : i < p.verts.length - 1) :
      incoming_cut_f (pathFlow p) {p.verts[i]} = p.bottleneck G G.source_not_sink := by
  simp only [incoming_cut_f, subset_univ, sum_sdiff_eq_sub, sum_singleton]
  have hz: ∀ v ≠ p.verts[i-1], pathFlow p v p.verts[i] = 0 := by
    intro v vnp
    rw [pathFlow]
    have : ¬ ∃ i_1, ∃ (h_1 : i_1 < p.verts.length - 1),
      v = p.verts[i_1] ∧ p.verts[i] = p.verts[i_1 + 1] := by
      push Not
      intro j hj ij con
      have iltlen : i < p.verts.length := by grind
      have jltlen : j + 1 < p.verts.length := by grind
      rw [ij] at vnp
      have : i = j+1 := eq_index_if_nodup p.verts i (j+1) iltlen jltlen con p.nodup
      grind
    simp [this]
  have : ∑ y, pathFlow p y p.verts[i] - pathFlow p p.verts[i] p.verts[i] =
    pathFlow p p.verts[i-1] p.verts[i] := by
    have : pathFlow p p.verts[i] p.verts[i] = 0 := by
      have h₁: i < p.verts.length := by grind
      have h₂: i - 1 < p.verts.length := by grind
      have h₃ : i ≠ i-1 := by grind
      simp [hz p.verts[i] (list_entry_neq_of_nodup p.verts i (i-1) h₁ h₂ h₃ p.nodup)]
    simp only [this, sub_zero]
    have zsum : ∑ y ≠ p.verts[i-1], pathFlow p y p.verts[i] = 0 := by
      apply sum_eq_zero; grind
    have : ∑ y, pathFlow p y p.verts[i] = pathFlow p p.verts[i-1] p.verts[i] +
      ∑ y ≠ p.verts[i-1], pathFlow p y p.verts[i] := by simp
    rw [this]; simp [zsum]
  have : pathFlow p p.verts[i - 1] p.verts[i] =
    p.toUVPath.bottleneck G G.source_not_sink := by
    rw [pathFlow]
    have : i - 1 < p.verts.length - 1 := by grind
    have : ∃ j, ∃ (hv : j < p.verts.length - 1), p.verts[i - 1] = p.verts[j] ∧
      p.verts[i] = p.verts[j+1] := by use i - 1, this; grind
    simp [this]
  grind

/-- An augmenting path induces a relaxed flow. -/
def augmentingPath.toFlow {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (p : augmentingPath G) : RelaxedFlow α G.toSTVertices where
  f := pathFlow p
  nonneg_flow := by
    intro u v; rw [pathFlow]
    by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i+1]
    · simp [h]; grind [pos_bottleneck_of_valid p G.source_not_sink]
    · simp [h]
  conservation := by
    intro u gns gnt
    by_cases h : ∃ (i : ℕ) (h : i < p.verts.length), u = p.verts[i]
    · obtain ⟨i, ⟨h', h''⟩⟩ := h
      have iltpm1 : i < p.verts.length - 1 := by grind [p.vend]
      have igt0 : i > 0 := by grind [p.ustart]
      have : outgoing_cut_f (pathFlow p) {u} = p.bottleneck G G.source_not_sink := by
        rw [h'']
        exact augmentingPath_flow_out p i iltpm1
      rw [this]
      have : incoming_cut_f (pathFlow p) {u} = p.bottleneck G G.source_not_sink := by
        rw [h'']
        exact augmentingPath_flow_in p i igt0 iltpm1
      rw [this]
    · grind [outgoing_cut_f, incoming_cut_f, pathFlow]
  no_edges_in_source := by
    intro u; rw [pathFlow]
    by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), u = p.verts[i] ∧ G.s = p.verts[i+1]
    · obtain ⟨i, ⟨h', ⟨_, h''⟩⟩⟩ := h
      have : p.verts[0] = p.verts[i+1] := by grind [p.ustart]
      exact absurd this (list_entry_neq_of_nodup p.verts 0 (i+1) (by grind) (by grind) (by simp)
        p.nodup)
    · simp [h]
  no_edges_out_sink := by
    intro v; rw [pathFlow]
    by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), G.t = p.verts[i] ∧ v = p.verts[i+1]
    · obtain ⟨i, ⟨h', ⟨h'', _⟩⟩⟩ := h
      have : p.verts[i] = p.verts[p.verts.length - 1] := by grind [p.vend]
      exact absurd this (list_entry_neq_of_nodup p.verts i (p.verts.length - 1)
        (by grind) (by grind) (by grind) p.nodup)
    · simp [h]

/-- The flow value of an augmenting path's induced flow equals its bottleneck. -/
lemma bottleneck_eq_augmentingPath_flow {V α : Type*} [Fintype V] [DecidableEq V] [Ring α]
    [LinearOrder α] {G : FlowNetwork V α} (p : augmentingPath G) :
      p.bottleneck G G.source_not_sink = flowValue G.toSTVertices p.toFlow := by
  rw [flowValue]
  have : G.s = p.verts[0]'(by grind [p.ustart]) := by grind [p.ustart]
  rw [augmentingPath.toFlow]
  simp_all only
  have := augmentingPath_flow_out p 0 (by grind [p.ustart, p.vend, G.source_not_sink])
  rw [this]

/-- The flow induced by an augmenting path is valid. -/
lemma augmentingPath.valid_toFlow {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} (p : augmentingPath G) : ValidFlow G p.toFlow := by
  simp only [ValidFlow, toFlow, pathFlow]
  intro u v
  by_cases h : ∃ i, ∃ (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i + 1]
  · simp only [h, ↓reduceIte]
    obtain ⟨i, ⟨h, ⟨rfl, rfl⟩⟩⟩ := h
    exact bottleneck_le_edge_flow G p.toUVPath G.source_not_sink i h
  · simp only [h, ↓reduceIte]; exact G.nonneg_capacity u v

open Classical in
/-- If F is a max flow, there is no augmenting path in its residual network. -/
lemma no_augmenting_of_max_flow' {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] {G : FlowNetwork V α} (F : RelaxedFlow α G.toSTVertices)
      (h : IsMaxFlow F) : augmentingPath (ResidualNetwork G F h.1) → False := by
  intro p
  have pos := pos_bottleneck_of_valid p G.source_not_sink
  have eqflow := bottleneck_eq_augmentingPath_flow p
  have valid := p.valid_toFlow
  have := no_augmenting_of_max_flow G F h p.toFlow valid
  have : flowValue G.toSTVertices p.toFlow > 0 := by
    have : G.toSTVertices = (ResidualNetwork G F h.1).toSTVertices := by rfl
    have := bottleneck_eq_augmentingPath_flow p
    have := pos_bottleneck_of_valid p G.source_not_sink
    grind
  grind

-- ============================================================
-- CONSTRUCTING THE MINIMUM CUT
-- ============================================================

/-- Extending a valid path u~>w by a fresh edge w→v yields a valid path u~>v.
  Requires v not already in the path (to preserve nodup). -/
lemma ValidUVPath.attachNode {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} {u w v : V} (p : ValidUVPath G u w) (hv : v ∉ p.verts.toFinset)
      (hedge : G.c w v > 0) : Nonempty (ValidUVPath G u v) := by
  let newverts := p.verts ++ [v]
  refine ⟨⟨⟨newverts, ?nonempty, ?nodup, ?ustart, ?vend⟩, ?valid⟩⟩
  · exact List.concat_ne_nil v p.verts
  · simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, List.mem_cons, or_false, ne_eq, forall_eq, true_and, newverts]
    rw [List.mem_toFinset] at hv
    constructor
    · exact p.nodup
    · exact fun a a_1 ↦ ne_of_mem_of_not_mem a_1 hv
  · grind only [= List.head_append_of_ne_nil, p.ustart]
  · exact List.getLast_concat
  · intro i
    by_cases h' : i < p.verts.length - 1
    · simp only [gt_iff_lt]
      intro h''
      dsimp [newverts]
      by_cases h''' : i <= p.verts.length - 2
      · have := p.valid i h'
        grind
      · push Not at h'''
        have : i = p.verts.length - 2 := by
          refine Nat.le_antisymm ?_ ?_
          · grind
          · grind
        grind
    · grind [p.vend]

/-- Given a path u~>w and a vertex v already on the path, extract the prefix path u~>v. -/
lemma ValidUVPath.prefix {V α : Type*} [Fintype V] [DecidableEq V] [Ring α] [LinearOrder α]
    {G : FlowNetwork V α} {u w : V} (p : ValidUVPath G u w) {v : V} (hv : v ∈ p.verts.toFinset) :
      Nonempty (ValidUVPath G u v) := by
  rw [List.mem_toFinset] at hv
  obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hv
  refine ⟨⟨⟨p.verts.take (i + 1), ?_, p.nodup.take, ?_, ?_⟩, ?_⟩⟩
  · simp only [ne_eq, List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or];
    exact p.nonempty
  · simp [List.head_take, p.ustart]
  · rw [List.getLast_take]; simp_all only [add_tsub_cancel_right, getElem?_pos, Option.getD_some]
  · intro j hj
    have hj' : j < p.verts.length - 1 := by simp [List.length_take] at hj; omega
    simp only [List.getElem_take, gt_iff_lt]; exact p.valid j hj'

open Classical in
/-- If s can reach u in the residual and there is a residual edge u → v, then s can reach v. -/
lemma reach_extend {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} {F : RelaxedFlow α G.toSTVertices} {h : ValidFlow G F} {u v : V}
      (hu : Nonempty (ValidUVPath (ResidualNetwork G F h) G.s u))
        (hedge : (ResidualNetwork G F h).c u v > 0) :
          Nonempty (ValidUVPath (ResidualNetwork G F h) G.s v) := by
  obtain ⟨p⟩ := hu
  by_cases hv : v ∈ p.verts.toFinset
  · exact p.prefix hv
  · exact p.attachNode hv hedge

/-- No augmenting path: t is not reachable from s via a valid path in the residual network. -/
def NoAugmentingPath {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) (h : ValidFlow G F) : Prop :=
  ¬ Nonempty (augmentingPath (ResidualNetwork G F h))

open Classical in
/-- The set of vertices reachable from s via a valid path in the residual network. -/
noncomputable def mkCutSet {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G F) : Finset V :=
  Finset.univ.filter (fun x => Nonempty (ValidUVPath (ResidualNetwork G F h) G.s x))

open Classical in
/-- Construct a cut from the reachable set when there is no augmenting path. -/
noncomputable def mkCutFromS {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G F) (hno : NoAugmentingPath G F h) : Cut G :=
  { S  := mkCutSet G F h
    T  := Finset.univ \ mkCutSet G F h
    hT := by ext a : 1; simp_all only [mem_sdiff, mem_univ, true_and]
    sins := by
      simp only [mkCutSet, mem_filter, mem_univ, true_and]
      exact ⟨⟨[G.s], by simp, by simp, by simp, by simp⟩, fun i hi => by simp at hi⟩
    tint := by
      simp only [mem_sdiff, mem_univ, true_and, mkCutSet, mem_filter]
      exact hno }

/-- Every forward arc from S to T is saturated. -/
lemma saturated_forward_arcs {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G F) :
        ∀ v w : V, v ∈ mkCutSet G F h → w ∉ mkCutSet G F h → F.f v w = G.c v w := by
  intro u v huS hvnS
  simp only [mkCutSet, mem_filter, mem_univ, true_and] at huS hvnS
  apply le_antisymm (h u v)
  by_contra hlt
  push Not at hlt
  have hres : (ResidualNetwork G F h).c u v > 0 := by
    simp only [ResidualNetwork]; grind [F.nonneg_flow v u]
  exact hvnS (reach_extend huS hres)

/-- Every backward arc from T to S carries zero flow. -/
lemma zero_backward_arcs {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) (h : ValidFlow G F) :
      ∀ v w : V, v ∉ mkCutSet G F h → w ∈ mkCutSet G F h → F.f v w = 0 := by
  intro v w hvnS hwS
  by_contra hne
  simp only [mkCutSet, mem_filter, mem_univ, true_and] at hwS hvnS
  have hpos : F.f v w > 0 := lt_of_le_of_ne (F.nonneg_flow v w) (Ne.symm hne)
  have hres : (ResidualNetwork G F h).c w v > 0 := by
    simp only [ResidualNetwork]; grind [F.nonneg_flow w v, h w v]
  exact hvnS (reach_extend hwS hres)

/-- When there is no augmenting path, the flow value equals the cut capacity. -/
lemma flow_eq_cut_cap {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) (h : ValidFlow G F)
      (hno : NoAugmentingPath G F h) : let C := mkCutFromS G F h hno
        flowValue G.toSTVertices F = cutCap C := by
  classical
  let C := mkCutFromS G F h hno
  rw [flow_value_eq_net_flow C F]
  apply Finset.sum_congr rfl; intro v hv
  apply Finset.sum_congr rfl; intro w hw
  have hv' : v ∈ mkCutSet G F h := hv
  have hw' : w ∉ mkCutSet G F h := by simp_all only [mem_sdiff, mem_univ, true_and, C]; exact hw
  rw [zero_backward_arcs G F h w v hw' hv', sub_zero]
  exact saturated_forward_arcs G F h v w hv hw'

/-- If F is a max flow, there is no augmenting path. -/
lemma no_augmenting_path_of_max_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : IsMaxFlow F) : NoAugmentingPath G F h.1 :=
  fun ⟨p⟩ => no_augmenting_of_max_flow' F h p

-- ============================================================
-- MAX FLOW ATTAINED (ℤ)
-- ============================================================

open Classical in
/-- The S-T cut whose S consists of only the source -/
noncomputable
def sCut {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) : Cut G where
  S := {G.s}
  T := univ \ {G.s}
  hT := rfl
  sins := by simp only [mem_singleton]
  tint := by grind [G.source_not_sink]

/-- For an integer flow network setting, there is a flow that attains the maximum flow -/
lemma ex_max_flow_Z {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) :
    ∃ F : RelaxedFlow ℤ G.toSTVertices, IsMaxFlow F := by
  let B : ℤ := cutCap (sCut G)
  have bound : ∀ F : RelaxedFlow ℤ G.toSTVertices, ValidFlow G F →
    flowValue G.toSTVertices F ≤ B := by intro F val; exact weak_duality (sCut G) F val
  have improv : ∀ F : RelaxedFlow ℤ G.toSTVertices, ValidFlow G F → ¬ IsMaxFlow F →
    ∃ F', ValidFlow G F' ∧ flowValue G.toSTVertices F' >= flowValue G.toSTVertices F + 1 := by
    intro F val nmax
    dsimp [IsMaxFlow] at nmax
    simp only [val, true_and, not_forall, not_le] at nmax
    obtain ⟨F', ⟨val', lt⟩⟩ := nmax
    use F'
    refine ⟨val', lt⟩
  let F0 : RelaxedFlow ℤ G.toSTVertices := trivialFlow G.toSTVertices
  have hF0 : ValidFlow G F0 := valid_flow_of_trivialFlow G
  let P : ℕ → Prop := fun n =>
    ∃ F : RelaxedFlow ℤ G.toSTVertices,
    ValidFlow G F ∧
    flowValue G.toSTVertices F ≥ n
  have hP0 : P 0 := by
    refine ⟨F0, hF0, ?_⟩
    simp [F0, zero_flowValue_of_trivialFlow]
  have hstep :
    ∀ n : ℕ, P n →
      (∃ F : RelaxedFlow ℤ G.toSTVertices, IsMaxFlow F) ∨ P (n + 1) := by
    intro n hn
    rcases hn with ⟨F, hvalid, hval⟩
    by_cases hmax : IsMaxFlow F
    · exact Or.inl ⟨F, hmax⟩
    · rcases improv F hvalid hmax with ⟨F', hvalid', himprov⟩
      right
      refine ⟨F', hvalid', ?_⟩
      have hnz : (n : ℤ) ≤ flowValue G.toSTVertices F := by
        exact_mod_cast hval
      grind
  have hBnonneg : B ≥ 0 := by
    have := bound F0 hF0
    simp only [zero_flowValue_of_trivialFlow, F0] at this
    exact this
  let N : ℕ := Int.toNat B + 1
  have : (∃ F : RelaxedFlow ℤ G.toSTVertices, IsMaxFlow F) ∨ P N := by
    induction N with
    | zero => exact Or.inr hP0
    | succ n ih => cases ih with
      | inl h => exact Or.inl h
      | inr hPn =>
        exact hstep n hPn
  cases this with
  | inl h => exact h
  | inr hPN =>
    rcases hPN with ⟨F, hvalid, hlarge⟩
    exfalso
    have hupper := bound F hvalid
    have hN : (N : ℤ) = B + 1 := by
      dsimp [N]
      rw [Int.toNat_of_nonneg hBnonneg]
    have : B + 1 ≤ B := by
      linarith [hupper]
    linarith

-- ============================================================
-- MAX FLOW ATTAINED (ℝ)
-- ============================================================

/-- The set of valid flows, now written as a set that satisfy a predicate rather than a structure -/
def FeasibleFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) : Set (V → V → ℝ) :=
  { f |
      (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, f u v ≤ G.c u v) ∧
      (∀ v, v ≠ G.s → v ≠ G.t →
          outgoing_cut_f f {v} = incoming_cut_f f {v}) ∧
      (∀ u, f u G.s = 0) ∧
      (∀ u, f G.t u = 0) }

/-- Equivalent definition of the value of a flow without a flow structure -/
noncomputable
def flowValueFn {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) : (V → V → ℝ) → ℝ :=
  fun f => outgoing_cut_f f {G.s}

/-- The set of functions that satisfy the capacity constraints -/
def capSatFnSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) : Set (V → V → ℝ) :=
  { f | ∀ u v, f u v ∈ Set.Icc (0 : ℝ) (G.c u v) }

/-- The set of feasible flows is a subset of
  the set of functions that satisfy the capacity constraints -/
lemma feasible_subset_capSat {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    FeasibleFlowSet G ⊆ capSatFnSet G := by
  intro f hf u v
  exact ⟨hf.1 u v, hf.2.1 u v⟩

/-- outgoing_cut_f is continuous in perturbations of the input function -/
lemma continuous_outgoing_cut_f {V : Type*} [Fintype V] (S : Finset V) :
    Continuous (fun f : V → V → ℝ => outgoing_cut_f f S) := by
  simp [outgoing_cut_f]
  continuity

/-- incoming_cut_f is continuous in perturbations of the input function -/
lemma continuous_incoming_cut_f {V : Type*} [Fintype V] (S : Finset V) :
    Continuous (fun f : V → V → ℝ => incoming_cut_f f S) := by
  simp [incoming_cut_f]
  continuity

/-- The value of a flow is continuous in perturbations of the flow -/
lemma continuous_flowValueFn {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    Continuous (flowValueFn G) := continuous_outgoing_cut_f {G.s}

/-- The set of feasible flows is closed -/
lemma closed_feasibleFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    IsClosed (FeasibleFlowSet G) := by
  simp only [FeasibleFlowSet, ne_eq]
  have hnonneg : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
      isClosed_iInter (fun v => isClosed_le continuous_const (continuous_apply_apply u v))))
  have hcap : IsClosed {f : V → V → ℝ | ∀ u v, f u v ≤ G.c u v} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
      isClosed_iInter (fun v => isClosed_le (continuous_apply_apply u v) continuous_const)))
  have hcons : IsClosed {f : V → V → ℝ | ∀ v, v ≠ G.s → v ≠ G.t → outgoing_cut_f f {v} =
    incoming_cut_f f {v}} := by simpa [Set.setOf_forall] using (isClosed_iInter (fun v =>
      isClosed_iInter (fun hs => isClosed_iInter (fun ht =>
        isClosed_eq (continuous_outgoing_cut_f {v}) (continuous_incoming_cut_f {v})))))
  have hsource : IsClosed {f : V → V → ℝ | ∀ u, f u G.s = 0} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
        isClosed_eq (continuous_apply_apply u G.s) continuous_const))
  have hsink : IsClosed {f : V → V → ℝ | ∀ u, f G.t u = 0} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
        isClosed_eq (continuous_apply_apply G.t u) continuous_const))
  exact hnonneg.inter (hcap.inter (hcons.inter (hsource.inter hsink)))

/-- The set of functions that satisfy capacity constraints is compact -/
lemma compact_capSatFnSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    IsCompact (capSatFnSet G) := by
  unfold capSatFnSet
  simp only [Set.mem_Icc]
  simpa [Set.pi, Set.iInter] using
    (isCompact_univ_pi fun u =>
      isCompact_univ_pi fun v =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (G.c u v))))

/-- The set of feasible functions is compact -/
lemma compact_feasibleFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    IsCompact (FeasibleFlowSet G) :=
  (compact_capSatFnSet G).of_isClosed_subset (closed_feasibleFlowSet G) (feasible_subset_capSat G)

/-- The set of feasible flows is nonempty -/
lemma feasibleFlowSet_nonempty {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    (FeasibleFlowSet G).Nonempty := by
  use ((trivialFlow G.toSTVertices).f)
  simp only [trivialFlow]
  rw [FeasibleFlowSet]
  simp only [ne_eq, outgoing_cut_f, subset_univ, sum_sdiff_eq_sub, sum_singleton, sum_sub_distrib,
    incoming_cut_f, sub_left_inj, Set.mem_setOf_eq, Std.le_refl, implies_true, G.nonneg_capacity,
    sum_const_zero, and_self]

/-- For a flow network over reals setting, there is a flow that attains the maximum flow in the
      predicate setting -/
lemma ex_max_flow_R' {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    ∃ f ∈ FeasibleFlowSet G, ∀ g ∈ FeasibleFlowSet G, flowValueFn G g ≤ flowValueFn G f := by
  rcases (compact_feasibleFlowSet G).exists_isMaxOn (feasibleFlowSet_nonempty G)
    (continuous_flowValueFn G).continuousOn with ⟨f, hfF, hmax⟩
  use f, hfF
  intro _ hgF
  exact hmax hgF

/-- Any valid flow from the structure defintion is a feasible flow in the predicate definition -/
lemma flow_toFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ)
    (g : RelaxedFlow ℝ G.toSTVertices) (gval : ValidFlow G g) : g.f ∈ FeasibleFlowSet G := by
  rw [ValidFlow] at gval
  simp only [FeasibleFlowSet, ne_eq, Set.mem_setOf_eq, g.nonneg_flow, implies_true, gval,
    g.no_edges_in_source, g.no_edges_out_sink, and_self, and_true, true_and]
  intro v vngs vngt
  exact g.conservation v vngs vngt

/-- For a flow network over reals setting, there is a flow that attains the maximum flow -/
lemma ex_max_flow_R {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    ∃ F : RelaxedFlow ℝ G.toSTVertices, IsMaxFlow F := by
  obtain ⟨g, gfeas, gopt⟩ := ex_max_flow_R' G
  rw [FeasibleFlowSet] at gfeas
  use ⟨g, by grind, by grind, by grind, by grind⟩
  rw [IsMaxFlow]
  constructor
  · grind [ValidFlow]
  · intro fn fnfeas
    have := gopt fn.f (flow_toFlowSet G fn fnfeas)
    rw [flowValueFn, flowValueFn] at this
    rw [flowValue, flowValue]
    simp only [ge_iff_le]
    exact this

-- ============================================================
-- MAX FLOW MIN CUT THEOREM
-- ============================================================

/-- The max-flow min-cut theorem: the maximum flow value equals the minimum cut capacity. -/
theorem max_flow_iff_eq_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlow G F) : IsMaxFlow F ↔
        ∃ C : Cut G, IsMinCut G C ∧ flowValue G.toSTVertices F = cutCap C := by
  constructor
  · -- forward
    intro hmax
    classical
    have hno : NoAugmentingPath G F hmax.1 := fun ⟨p⟩ => no_augmenting_of_max_flow' F hmax p
    let C := mkCutFromS G F hmax.1 hno
    exact ⟨C, fun C' => by grind [flow_eq_cut_cap G F hmax.1 hno, weak_duality C' F hmax.1],
              flow_eq_cut_cap G F hmax.1 hno⟩
  · --reverse
    rintro ⟨C, _, heq⟩
    exact max_flow_of_flow_value_eq_cut C F h heq

/-- Corollary: every maximum flow witnesses a minimum cut with equal value. -/
theorem max_flow_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) (h : IsMaxFlow F) :
      ∃ C : Cut G, IsMinCut G C ∧ flowValue G.toSTVertices F = cutCap C :=
  (max_flow_iff_eq_min_cut G F h.1).mp h

/-- For flow types that have proofs that the max flow is attained,
  a stronger version of min-cut max-flow theorem that states that
  there exist a maximum flow and a minimum cut with equal value -/
lemma ex_max_flow_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (h : ∃ F : RelaxedFlow α G.toSTVertices, IsMaxFlow F) :
      ∃ (F : RelaxedFlow α G.toSTVertices), ∃ C : Cut G,
  IsMaxFlow F ∧ IsMinCut G C ∧ flowValue G.toSTVertices F = cutCap C := by
    obtain ⟨F, hF⟩ := h
    obtain ⟨C, hC⟩ := max_flow_min_cut G F hF
    use F, C

/-- There exist a maximum flow and a minimum cut with equal value (ℝ version). -/
lemma ex_max_flow_min_cut_R {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
    ∃ (F : RelaxedFlow ℝ G.toSTVertices), ∃ C : Cut G,
      IsMaxFlow F ∧ IsMinCut G C ∧ flowValue G.toSTVertices F = cutCap C :=
  ex_max_flow_min_cut G <| ex_max_flow_R G

/-- There exist a maximum flow and a minimum cut with equal value (ℤ version). -/
lemma ex_max_flow_min_cut_Z {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) :
    ∃ (F : RelaxedFlow ℤ G.toSTVertices), ∃ C : Cut G,
      IsMaxFlow F ∧ IsMinCut G C ∧ flowValue G.toSTVertices F = cutCap C :=
  ex_max_flow_min_cut G <| ex_max_flow_Z G

-- ============================================================
-- MAX FLOW MIN CUT THEOREM (natural numbers edition)
-- ============================================================

structure NatFlowNetwork (V : Type*) [Fintype V] extends STVertices V where
  c : V → V → ℕ

def NatFlowNetwork.toFlowNetwork {V : Type*} [Fintype V]
    (G : NatFlowNetwork V) : FlowNetwork V ℤ where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c := fun u v => (G.c u v : ℤ)
  nonneg_capacity := by
    norm_num

theorem max_flow_iff_eq_min_cut_N {V : Type*} [Fintype V] (G : NatFlowNetwork V)
    (F : RelaxedFlow ℤ G.toSTVertices) (h : ValidFlow G.toFlowNetwork F) :
      IsMaxFlow (G := G.toFlowNetwork) F ↔
        ∃ C : Cut G.toFlowNetwork, IsMinCut G.toFlowNetwork C ∧
          flowValue G.toSTVertices F = cutCap C :=
  max_flow_iff_eq_min_cut G.toFlowNetwork F h

-- ===========================================================
-- UNDIRECTED MAX FLOW MIN CUT THEOREM
-- ===========================================================

/-- Augmentation cancels out any 2-cycles: flow can't go both ways after augmentation -/
lemma no_bidirectional_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : STVertices V) :
      ∀ F F' : RelaxedFlow α G, ∀ u v, (F ⋄ F').f u v = 0 ∨ (F ⋄ F').f v u = 0 := by
  intro F F' u v
  simp only [(· ⋄ ·), sup_eq_right, tsub_le_iff_right, zero_add]
  have : F'.f v u + F.f v u = F.f v u + F'.f v u := by grind
  rw [this]
  have : F'.f u v + F.f u v = F.f u v + F'.f u v := by grind
  rw [this]
  exact le_total (F.f u v + F'.f u v) (F.f v u + F'.f v u)

/-- An undirected flow network can be modeled as a directed flow network
  where flow can only go in 1 direction -/
structure Undirected_FlowNetwork (V α : Type*) [Fintype V] [Ring α] [LinearOrder α] extends
    FlowNetwork V α where
  c_symm : ∀ u v, c u v = c v u

/-- A valid undirected flow additionally requires that flow can only go in 1 direction:
  no 2-cycles are allowed -/
def ValidFlowUndirected (V α : Type*) [Fintype V] [Ring α] [LinearOrder α]
    (G : Undirected_FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) : Prop :=
  (ValidFlow G.toFlowNetwork F) ∧ (∀ u v, F.f u v = 0 ∨ F.f v u = 0)

/-- An undirected flow is maximal if it's a valid undirected flow and its flow value is
  no less than any other valid undirected flow -/
def is_max_undirected_flow {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    {G : Undirected_FlowNetwork V α} (fn : RelaxedFlow α G.toSTVertices) : Prop :=
  ValidFlowUndirected V α G fn ∧
    ∀ fn' : RelaxedFlow α G.toSTVertices, ValidFlowUndirected V α G fn' →
      flowValue G.toSTVertices fn' ≤ flowValue G.toSTVertices fn

/-- Any undirected maximal flow is also a directed maximal flow -/
lemma undirected_max_directed_max {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices) :
      is_max_undirected_flow F → IsMaxFlow F := by
  intro h
  constructor
  · exact h.1.1
  · intro fn valfn
    have : flowValue G.toSTVertices fn =
      flowValue G.toSTVertices (fn ⋄ (trivialFlow G.toSTVertices)) := by simp [add_flow]
    rw [this]
    apply h.2
    constructor
    · exact valid_augmentation_of_trivialFlow G.toFlowNetwork _ valfn
    · exact no_bidirectional_flow G.toSTVertices fn (trivialFlow G.toSTVertices)

/-- The max-flow min-cut theorem: the maximum flow value equals the minimum cut capacity. -/
theorem undirected_max_flow_iff_eq_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : ValidFlowUndirected V α G F) : is_max_undirected_flow F ↔ ∃ C : Cut G.toFlowNetwork,
        IsMinCut G.toFlowNetwork C ∧ flowValue G.toSTVertices F = cutCap C := by
  constructor
  · -- forward
    intro h'
    have : IsMaxFlow F := undirected_max_directed_max G F h'
    obtain ⟨C, hC, FCeq⟩ := max_flow_min_cut G.toFlowNetwork F this
    use C
  · --reverse
    rintro ⟨C, mC, heq⟩
    constructor
    · exact h
    · intro fn valfn
      have := max_flow_iff_eq_min_cut G.toFlowNetwork F h.1
      have h' := this.mpr
      have : (∃ C, IsMinCut G.toFlowNetwork C ∧ flowValue G.toSTVertices F = cutCap C) := by
        use C
      have := h' this
      exact this.2 fn valfn.1

/-- every maximum flow witnesses a minimum cut with equal value -/
theorem undirected_max_flow_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α) (F : RelaxedFlow α G.toSTVertices)
      (h : is_max_undirected_flow F) : ∃ C, IsMinCut G.toFlowNetwork C ∧
        flowValue G.toSTVertices F = cutCap C := (undirected_max_flow_iff_eq_min_cut G F h.1).mp h

theorem ex_undirected_max_flow_min_cut {V α : Type*} [Fintype V] [Ring α] [LinearOrder α]
    [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α) (h : ∃ F C, IsMaxFlow F ∧
      IsMinCut G.toFlowNetwork C ∧ flowValue G.toSTVertices F = cutCap C) : ∃ F C,
        is_max_undirected_flow F ∧ IsMinCut G.toFlowNetwork C ∧ flowValue G.toSTVertices F =
          cutCap C := by
  obtain ⟨F, C, hF, hC, FCeq⟩ := h
  use F ⋄ (trivialFlow G.toSTVertices), C
  constructor
  · constructor
    · rw [ValidFlowUndirected]
      constructor
      · exact valid_augmentation_of_trivialFlow G.toFlowNetwork F hF.1
      · exact no_bidirectional_flow G.toSTVertices F (trivialFlow G.toSTVertices)
    · intro fn vfn;
      rw [IsMaxFlow] at hF
      simp [add_flow, hF.2 fn vfn.1]
  · constructor
    · exact hC
    · simp [add_flow, FCeq]

/-- An equivalent for the max flow min cut theorem for ℤ for undirected flow networks -/
theorem ex_undirected_max_flow_min_cut_Z {V : Type*} [Fintype V] (G : Undirected_FlowNetwork V ℤ) :
    ∃ F C, is_max_undirected_flow F ∧ IsMinCut G.toFlowNetwork C ∧
      flowValue G.toSTVertices F = cutCap C := ex_undirected_max_flow_min_cut G <|
        ex_max_flow_min_cut_Z G.toFlowNetwork

/-- An equivalent for the max flow min cut theorem for ℝ for undirected flow networks -/
theorem ex_undirected_max_flow_min_cut_R {V : Type*} [Fintype V] (G : Undirected_FlowNetwork V ℝ) :
    ∃ F C, is_max_undirected_flow F ∧ IsMinCut G.toFlowNetwork C ∧
      flowValue G.toSTVertices F = cutCap C := ex_undirected_max_flow_min_cut G <|
        ex_max_flow_min_cut_R G.toFlowNetwork
