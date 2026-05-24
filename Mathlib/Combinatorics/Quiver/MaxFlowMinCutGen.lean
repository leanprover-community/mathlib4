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
structure FlowNetwork (V : Type*) (α : Type*) [Ring α] [LinearOrder α] [Fintype V] extends STVertices V where
  c : V → V → α
  nonneg_capacity : ∀ u v : V, c u v ≥ 0

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going into S -/
noncomputable
def mk_in {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α]
    (f : V → V → α) (S : Finset V) : α :=
  ∑ x ∈ Finset.univ \ S, ∑ y ∈ S, f x y

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going out of S -/
noncomputable
def mk_out {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α]
    (f : V → V → α) (S : Finset V) : α :=
  ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, f x y

/-- A relaxedFlow is defined on a complete graph with source and sink and assigns to each edge
  a nonnegative flow value that satisfies flow conservation and does not send flow into the
  source or out of the sink. -/
structure RelaxedFlow (V : Type*) (α : Type*) [Ring α] [LinearOrder α] [Fintype V] (G : STVertices V) where
  f : V → V → α
  nonneg_flow : ∀ u v : V, f u v ≥ 0
  conservation : ∀ v : V, v ≠ G.s → v ≠ G.t → mk_out f {v} = mk_in f {v}
  no_edges_in_source : ∀ u : V, f u G.s = 0
  no_edges_out_sink : ∀ u : V, f G.t u = 0

open Classical in
/-- An S-T cut partitions the set of vertices into a set S that
 contains the source and a set T that contains the sink. -/
structure Cut (V : Type*) (α : Type*) [Ring α] [LinearOrder α] [Fintype V] (G : FlowNetwork V α) where
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
def ValidFlow
(V : Type*) [Fintype V] (α : Type*) [Ring α] [LinearOrder α] (G : FlowNetwork V α) (g : RelaxedFlow V α G.toSTVertices) : Prop :=
  ∀ u v : V, g.f u v ≤ G.c u v

/-- An (explicit) equivalent definition for flow conservation. -/
lemma eq_conservation (V : Type*) [Fintype V] (α : Type*) [Ring α] [LinearOrder α] (G : STVertices V) (flow : RelaxedFlow V α G) :
 ∀ v : V, v ≠ G.s → v ≠ G.t → ∑ x, (flow.f x v - flow.f v x) = 0 := by
  intro v vns vnt
  have : mk_out flow.f {v} = mk_in flow.f {v} := flow.conservation v vns vnt
  unfold mk_in mk_out at this
  simp at this
  simp [this]

/-- The addition/augmentation of a flow with another. Implicitly cancels out any 2-cycles,
  guaranteeing that flow cannot move between two vertices in both directions. This is
  necessary to guarantee augmenting a valid flow from the original network with the residual
  network results in a valid flow in the original network. -/
instance (V : Type*) (α : Type*) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V]  (G : STVertices V) : Mul (RelaxedFlow V α G) where
  mul g h := {
    f u v := max (g.f u v + h.f u v - g.f v u - h.f v u) 0
    nonneg_flow := by simp
    conservation := by
      intro v vns vnt
      simp only [mk_out, subset_univ, sum_sdiff_eq_sub, sum_singleton, sum_sub_distrib,
      add_sub_cancel_left, sub_self, max_self, sub_zero, mk_in]
      have h₁: ∑ x, (max (g.f x v + h.f x v - g.f v x - h.f v x) 0
        - max (-(g.f x v + h.f x v - g.f v x - h.f v x)) 0) = 0 := by
        simp only [max_zero_sub_max_neg_zero_eq_self (g.f _ v + h.f _ v - g.f v _ - h.f v _)]
        calc
          ∑ x, (g.f x v + h.f x v - g.f v x - h.f v x)
          = ∑ x, (g.f x v - g.f v x) + ∑ x, (h.f x v - h.f v x) := by
            simp [Finset.sum_add_distrib]; grind
          _ = 0 := by
            simp only [add_eq_right, eq_conservation V α G g v vns vnt,
              eq_conservation V α G h v vns vnt];
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

/-- The value of a flow: the amount of flow going out of the sink. -/
noncomputable
def Flow_value {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V)
    (flow : RelaxedFlow V α G) : α := mk_out flow.f {G.s}

/-- The value of a flow is nonnegative. -/
lemma nonneg_flow_value {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V) :
  ∀F : RelaxedFlow V α G, Flow_value G F ≥ 0 := by
  intro F; simp [Flow_value, mk_out, F.no_edges_in_source, sum_nonneg, F.nonneg_flow]

/-- The value of a flow is additive under augmentation. -/
lemma add_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V) (flow₁ flow₂ : RelaxedFlow V α G) :
  Flow_value G (flow₁ * flow₂) = Flow_value G flow₁ + Flow_value G flow₂ := by
  have: ∀ x, (flow₁.f G.s x + flow₂.f G.s x) ≥ 0 := by
    intro x; grind [flow₁.nonneg_flow G.s x, flow₂.nonneg_flow G.s x]
  simp [Flow_value, (· * ·), Mul.mul, mk_out,
   flow₁.no_edges_in_source, flow₂.no_edges_in_source, this, sum_add_distrib]

/-- The capacity of an S-T cut is the sum of edge capacities of edges going from S to T. -/
noncomputable
def cut_cap {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] {G : FlowNetwork V α}
    (c : Cut V α G) : α := mk_out G.c c.S

/-- The flow of an S-T cut given a RelaxedFlow is the sum of flows going over edges going
  from S to T. -/
noncomputable
def cut_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] {G : FlowNetwork V α}
  (g : RelaxedFlow V α G.toSTVertices)
    (c : Cut V α G) : α := mk_out g.f c.S

/-- A flow is maximal if it respects capacities and has the largest flow value compared to
 other flows that respect capacities. -/
def is_max_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] {G : FlowNetwork V α}
    (fn : RelaxedFlow V α G.toSTVertices) : Prop :=
  ValidFlow V α G fn ∧ ∀ fn' : RelaxedFlow V α G.toSTVertices, ValidFlow V α G fn' →
    Flow_value G.toSTVertices fn' ≤ Flow_value G.toSTVertices fn

/-- A cut is minimal if its capapcity is minimal. -/
def is_min_cut {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α)
    (fn : Cut V α G) : Prop :=
  ∀ fn' : Cut V α G, cut_cap fn ≤ cut_cap fn'

/-- The residual network is a flow network defined using an existing flow network and flow.
  It uses the same source and sink. The capacity of an edge u v is given by its original capacity
  minus the amount of flow going over this edge plus the amount of flow going in the opposite
  direction. -/
def ResidualNetwork {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α) (F : RelaxedFlow V α G.toSTVertices)
  (h : ValidFlow V α G F) : FlowNetwork V α where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c u v := G.c u v - F.f u v + F.f v u
  nonneg_capacity := by intro u v; rw [ge_iff_le]; grind [h u v, F.nonneg_flow v u]

/-- Augmenting a valid flow in the original network with a valid flow in its residual network
  results in a new valid flow. -/
lemma valid_augmentation {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α)
  (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) :
  ∀F' : (RelaxedFlow V α G.toSTVertices), ValidFlow V α (ResidualNetwork G F h) F' →
  ∀ u v : V, (F * F').f u v ≤ G.c u v := by
  intro F' val_F' u v
  simp [(· * ·), Mul.mul]
  constructor
  · have : F'.f u v ≤ G.c u v - F.f u v + F.f v u := by exact val_F' u v
    grind [F'.nonneg_flow v u, F.nonneg_flow u v]
  · simp [G.nonneg_capacity u v]

/-- If a flow is maximal, all flows in its residual graph have value 0. -/
lemma max_flow_no_augmenting {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α)
  (F : RelaxedFlow V α G.toSTVertices) (h : is_max_flow F) :
  ∀F' : (RelaxedFlow V α G.toSTVertices), ValidFlow V α (ResidualNetwork G F h.1) F' →
  Flow_value G.toSTVertices F' = 0 := by
  intro F' g
  by_contra con
  push Not at con
  have: Flow_value G.toSTVertices F' > 0 := by
   apply lt_of_le_of_ne;
   · grind [nonneg_flow_value G.toSTVertices F']
   · symm; exact con
  let optF := F * F'
  have optge : Flow_value G.toSTVertices optF > Flow_value G.toSTVertices F := by calc
   Flow_value G.toSTVertices optF = Flow_value G.toSTVertices F + Flow_value G.toSTVertices F' :=
   by exact add_flow G.toSTVertices F F'
   _ > Flow_value G.toSTVertices F := by grind
  have optval : ValidFlow V α G optF := by
   apply valid_augmentation G F h.1 F' g
  have: ¬is_max_flow F := by
   simp only [is_max_flow, not_and, not_forall, not_le]; intro _; use optF;
  contradiction

-- ============================================================
-- WEAK DUALITY + OPTIMALITY CRITERION
-- ============================================================

/-- The flow of a cut is no more than the capacity of a cut. -/
lemma cut_flow_le_cut_cap {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α) (C : Cut V α G)
  (g : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G g) :
  cut_flow g C ≤ cut_cap C := by
    simp only [cut_flow, cut_cap, mk_out]
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro w _
    exact h v w

open Classical in
/-- Flow conservation of the vertices in S without the source. -/
lemma helper {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α) (C : Cut V α G)
  (g : RelaxedFlow V α G.toSTVertices) :
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
    eq_conservation V α G.toSTVertices g v vns vnt]

/-- You can add a singleton value in the sum. -/
lemma helper2 {V : Type*} [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (S : Finset V) (a : V) (h : a ∈ S)
  (f : V → α) : f a + ∑ b ∈ S \ {a}, f b = ∑ b ∈ S, f b := by
  refine add_eq_of_eq_sub ?_
  have : ∑ b ∈ S, f b - ∑ b ∈ S \ {a}, f b = f a := by simp [h]
  rw [this]

/-- If summing over a subset evaluates to 0, you can that subset from the original sum. -/
lemma helper3 {V : Type*} [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (S : Finset V) (T : Finset V)
  (h : T ⊆ S) (f : V → α) (h' : ∑ x ∈ T, f x = 0) : ∑ b ∈ S, f b = ∑ b ∈ S \ T, f b := by
  simp [h, h']

open Classical in
/-- For any cut, the value of a flow is equal to the sum of flows over edges from S to T
  minus the flow over edges from T to S. -/
lemma flow_value_eq_net_flow {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (C : Cut V α G) (g : RelaxedFlow V α G.toSTVertices) :
    Flow_value G.toSTVertices g =
      ∑ v ∈ C.S, ∑ w ∈ univ \ C.S, (g.f v w - g.f w v) := by
  rw [← add_zero (Flow_value G.toSTVertices g), ← helper G C g]
  simp only [Flow_value, mk_out]
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
          rw [@helper2 V (Classical.decEq V) α _ _ _ C.S G.s C.sins
            (fun v => ∑ w, (g.f v w - g.f w v))]
    _ = ∑ v ∈ C.S, ∑ w ∈ univ \ C.S, (g.f v w - g.f w v) := by
          rw [sum_comm]
          have htmp := @helper3 V (Classical.decEq V) α _ _ _ univ C.S (subset_univ C.S)
            (fun v => ∑ w ∈ C.S, (g.f w v - g.f v w)) hinner
          rw [htmp, sum_comm]

/-- The value of a flow is no more than the flow of any cut. -/
lemma flow_le_cut_flow {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) (C : Cut V α G) (g : RelaxedFlow V α G.toSTVertices) :
    Flow_value G.toSTVertices g ≤ cut_flow g C := by
  classical
  rw [flow_value_eq_net_flow G C g]
  simp only [cut_flow, mk_out]
  apply Finset.sum_le_sum; intro v _
  apply Finset.sum_le_sum; intro w _
  grind [g.nonneg_flow w v]

/-- The value of a flow is no more than the capacity of any cut. -/
theorem weak_duality {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α) (C : Cut V α G)
  (g : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G g) :
  Flow_value G.toSTVertices g ≤ cut_cap C := by
  grind [cut_flow_le_cut_cap G C g h, flow_le_cut_flow G C g]

/-- If the value of a flow is equal to the capacity of any cut, the flow value is maximal. -/
lemma max_flow_if_eq_cut {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α) (C : Cut V α G)
  (g : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G g) :
  Flow_value G.toSTVertices g = cut_cap C → is_max_flow g := by
    intro h'
    constructor
    · exact h
    · rw [h']
      apply weak_duality

-- ===========================================================
-- TRIVIAL (ZERO) FLOWS
-- ===========================================================
/-- The trivial (zero) flow that doesn't send flow over any edge -/
def trivial_flow {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : STVertices V) : RelaxedFlow V α G where
  f := fun x y => 0
  nonneg_flow := by simp only [ge_iff_le, Std.le_refl, implies_true]
  conservation := by grind [mk_out, mk_in]
  no_edges_in_source := by simp only [implies_true]
  no_edges_out_sink := by simp only [implies_true]

/-- The trivial flow doesn't send any flow over an edge -/
@[simp]
lemma zero_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V) :
  ∀ x y, (trivial_flow G).f x y = (0 : α) := by simp [trivial_flow]

/-- The value of the trivial flow is 0 -/
@[simp]
lemma zero_trivial_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V) :
  Flow_value G (trivial_flow G) = (0 : α) := by
    simp only [Flow_value, mk_out, zero_flow, sum_const_zero]

/-- The trivial flow is always valid -/
lemma valid_zero_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α) :
  ValidFlow V α G (trivial_flow G.toSTVertices) := by
    simp only [ValidFlow, zero_flow, G.nonneg_capacity, implies_true]

/-- Augmenting a valid flow with the trivial flow results in a valid flow -/
lemma valid_zero_augmentation {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α)
  (F : RelaxedFlow V α G.toSTVertices) (validF : ValidFlow V α G F) :
  ValidFlow V α G (F * (trivial_flow G.toSTVertices)) := by
  rw [ValidFlow] at validF
  simp only [ValidFlow, HMul.hMul, Mul.mul, zero_flow, add_zero, sub_zero, sup_le_iff,
    tsub_le_iff_right, G.nonneg_capacity, and_true]
  intro u v
  trans G.c u v
  · exact validF u v
  · grind [F.nonneg_flow v u]

-- ============================================================
-- AUGMENTING PATHS
-- ============================================================

/-- A simple path from u to v, represented as a nodup list of vertices. -/
structure uvPath {V : Type*} [Fintype V] (u v : V) where
  verts : List V
  nonempty : verts ≠ []
  nodup : verts.Nodup
  ustart : verts.head nonempty = u
  vend : verts.getLast nonempty = v

/-- A valid path in a flow network: every consecutive pair has positive capacity. -/
structure validuvPath {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α) (u v : V)
  extends uvPath u v where
  valid : ∀ (i : ℕ) (h : i < verts.length - 1), G.c (verts[i]) (verts[i+1]) > 0

/-- An augmenting path is a valid path from s to t. -/
def augmentingPath {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α) :=
  validuvPath G G.s G.t

/-- A path between two distinct vertices has length at least 2 -/
lemma ge_two_vertices {V : Type*} [Fintype V] {u v : V} (p : uvPath u v) (h : u ≠ v) :
 p.verts.length ≥ 2 := by
  grind [p.ustart, p.vend]

/-- The bottleneck capacity of a path: the minimum edge capacity along it. -/
def uvPath.bottleneck {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (G : FlowNetwork V α) {u v : V} (p : uvPath u v) (h : u ≠ v) : α := by
    have : p.verts.length ≥ 2 := by apply ge_two_vertices p h
    have : p.verts.tail.length ≥ 1 := by grind
    let J := List.zipWith G.c p.verts p.verts.tail
    have : J.length ≥ 1 := by grind
    exact J.min (by grind)

/-- The bottleneck is not more than any of the capacities of edges in the path -/
lemma lb_bottleneck {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
  {u v : V} (p : uvPath u v) (h : u ≠ v) :
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
      rw [uvPath.bottleneck]
      exact List.min_le_of_mem hmem

/-- Some edge in the path has capacity equal to the bottleneck -/
lemma ub_bottleneck {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α) {u v : V}
  (p : uvPath u v) (h : u ≠ v) :
    ∃ (i : ℕ) (h' : i < p.verts.length - 1), p.bottleneck G h = G.c p.verts[i] p.verts[i+1] := by
  let xs := List.zipWith G.c p.verts p.verts.tail
  have : xs.length ≥ 1 := by grind [ge_two_vertices]
  have : xs.min (by grind) ∈ xs := by exact List.min_mem (uvPath.bottleneck._proof_3 G p this)
  use xs.idxOf (xs.min (by grind))
  have : List.idxOf (xs.min (by grind)) xs < p.verts.length - 1 := by grind
  use this
  have : uvPath.bottleneck G p h = xs.min (by grind) := by grind [uvPath.bottleneck]
  rw [this]
  let i := xs.idxOf (xs.min (by grind))
  have : xs[i]'(by grind) = xs.min (by grind) := by grind
  have : G.c p.verts[i] p.verts[i+1] = xs.min (by grind):= by grind
  grind

/-- The bottleneck of a valid path is positive. -/
lemma pos_bottleneck {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {G : FlowNetwork V α} {u v : V} (p : validuvPath G u v) (h : u ≠ v) :
    p.touvPath.bottleneck G h > 0 := by
    obtain ⟨i, ⟨h', h''⟩⟩ := ub_bottleneck G p.touvPath h
    grind [lb_bottleneck G p.touvPath h i h', p.valid i h']

/-- The flow induced by an augmenting path: send bottleneck flow along each edge of the path. -/
def pathFlow {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {G : FlowNetwork V α} (p : augmentingPath G) :
  V → V → α := fun a b => if ∃ (i : ℕ) (h : i < p.verts.length - 1),
    a = p.verts[i] ∧ b = p.verts[i+1] then p.bottleneck G G.source_not_sink else 0

/-- If a list has no duplicates, then no two distinct entries of it are equal -/
lemma neq_if_nodup {V : Type*} (l : List V) (i j : ℕ) (h₀ : i < l.length)
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
lemma pathlike_flow_out {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {G : FlowNetwork V α}
 (p : augmentingPath G) (i : ℕ) (h : i < p.verts.length - 1) :
 mk_out (pathFlow p) {p.verts[i]} = p.bottleneck G G.source_not_sink := by
  simp only [mk_out, subset_univ, sum_sdiff_eq_sub, sum_singleton]
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
      simp [hz p.verts[i] (neq_if_nodup p.verts i (i+1) h₁ h₂ h₃ p.nodup)]
    simp only [this, sub_zero]
    have zsum : ∑ y ≠ p.verts[i+1], pathFlow p p.verts[i] y = 0 := by
      apply sum_eq_zero; grind
    have : ∑ y, pathFlow p p.verts[i] y = pathFlow p p.verts[i] p.verts[i+1] +
      ∑ y ≠ p.verts[i+1], pathFlow p p.verts[i] y := by simp
    rw [this]; simp [zsum]
  have : pathFlow p p.verts[i] p.verts[i + 1] =
    uvPath.bottleneck G p.touvPath G.source_not_sink := by
    rw [pathFlow]
    have : ∃ j, ∃ (hv : j < p.verts.length - 1), p.verts[i] = p.verts[j] ∧
      p.verts[i + 1] = p.verts[j + 1] := by use i, h;
    simp [this]
  grind

/-- The amount of flow entering a vertex that is contained in an augmenting path equals
  the bottleneck of the augmenting path -/
lemma pathlike_flow_in {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {G : FlowNetwork V α}
 (p : augmentingPath G) (i : ℕ) (h₁ : i > 0) (h : i < p.verts.length - 1) :
 mk_in (pathFlow p) {p.verts[i]} = p.bottleneck G G.source_not_sink := by
  simp only [mk_in, subset_univ, sum_sdiff_eq_sub, sum_singleton]
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
      simp [hz p.verts[i] (neq_if_nodup p.verts i (i-1) h₁ h₂ h₃ p.nodup)]
    simp only [this, sub_zero]
    have zsum : ∑ y ≠ p.verts[i-1], pathFlow p y p.verts[i] = 0 := by
      apply sum_eq_zero; grind
    have : ∑ y, pathFlow p y p.verts[i] = pathFlow p p.verts[i-1] p.verts[i] +
      ∑ y ≠ p.verts[i-1], pathFlow p y p.verts[i] := by simp
    rw [this]; simp [zsum]
  have : pathFlow p p.verts[i - 1] p.verts[i] =
    uvPath.bottleneck G p.touvPath G.source_not_sink := by
    rw [pathFlow]
    have : i - 1 < p.verts.length - 1 := by grind
    have : ∃ j, ∃ (hv : j < p.verts.length - 1), p.verts[i - 1] = p.verts[j] ∧
      p.verts[i] = p.verts[j+1] := by use i - 1, this; grind
    simp [this]
  grind

/-- An augmenting path induces a relaxed flow. -/
def augmentingPath.toFlow {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} (p : augmentingPath G) : RelaxedFlow V α G.toSTVertices where
    f := pathFlow p
    nonneg_flow := by
      intro u v; rw [pathFlow]
      by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i+1]
      · simp [h]; grind [pos_bottleneck p G.source_not_sink]
      · simp [h]
    conservation := by
      intro u gns gnt
      by_cases h : ∃ (i : ℕ) (h : i < p.verts.length), u = p.verts[i]
      · obtain ⟨i, ⟨h', h''⟩⟩ := h
        have iltpm1 : i < p.verts.length - 1 := by grind [p.vend]
        have igt0 : i > 0 := by grind [p.ustart]
        have : mk_out (pathFlow p) {u} = p.bottleneck G G.source_not_sink := by
          rw [h'']
          exact pathlike_flow_out p i iltpm1
        rw [this]
        have : mk_in (pathFlow p) {u} = p.bottleneck G G.source_not_sink := by
          rw [h'']
          exact pathlike_flow_in p i igt0 iltpm1
        rw [this]
      · grind [mk_out, mk_in, pathFlow]
    no_edges_in_source := by
      intro u; rw [pathFlow]
      by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), u = p.verts[i] ∧ G.s = p.verts[i+1]
      · obtain ⟨i, ⟨h', ⟨_, h''⟩⟩⟩ := h
        have : p.verts[0] = p.verts[i+1] := by grind [p.ustart]
        exact absurd this (neq_if_nodup p.verts 0 (i+1) (by grind) (by grind) (by simp) p.nodup)
      · simp [h]
    no_edges_out_sink := by
      intro v; rw [pathFlow]
      by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), G.t = p.verts[i] ∧ v = p.verts[i+1]
      · obtain ⟨i, ⟨h', ⟨h'', _⟩⟩⟩ := h
        have : p.verts[i] = p.verts[p.verts.length - 1] := by grind [p.vend]
        exact absurd this (neq_if_nodup p.verts i (p.verts.length - 1)
          (by grind) (by grind) (by grind) p.nodup)
      · simp [h]

/-- The flow value of an augmenting path's induced flow equals its bottleneck. -/
lemma bottleneck_eq_flow {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {G : FlowNetwork V α} (p : augmentingPath G) :
  p.bottleneck G G.source_not_sink = Flow_value G.toSTVertices p.toFlow := by
  rw [Flow_value]
  have : G.s = p.verts[0]'(by grind [p.ustart]) := by grind [p.ustart]
  rw [augmentingPath.toFlow]
  simp_all only
  have := pathlike_flow_out p 0 (by grind [p.ustart, p.vend, G.source_not_sink])
  rw [this]

/-- The flow induced by an augmenting path is valid. -/
lemma augmentingPath.valid_toFlow {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {G : FlowNetwork V α} (p : augmentingPath G) : ValidFlow V α G p.toFlow := by
  simp only [ValidFlow, toFlow, pathFlow]
  intro u v
  by_cases h : ∃ i, ∃ (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i + 1]
  · simp only [h, ↓reduceIte]
    obtain ⟨i, ⟨h, ⟨rfl, rfl⟩⟩⟩ := h
    exact lb_bottleneck G p.touvPath G.source_not_sink i h
  · simp only [h, ↓reduceIte]; exact G.nonneg_capacity u v

/-- If F is a max flow, there is no augmenting path in its residual network. -/
lemma max_flow_no_augmenting' {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} (F : RelaxedFlow V α G.toSTVertices) (h : is_max_flow F) :
      augmentingPath (ResidualNetwork G F h.1) → False := by
  intro p
  have pos := pos_bottleneck p G.source_not_sink
  have eqflow := bottleneck_eq_flow p
  have valid := p.valid_toFlow
  have := max_flow_no_augmenting G F h p.toFlow valid
  have : Flow_value G.toSTVertices p.toFlow > 0 := by
    have : G.toSTVertices = (ResidualNetwork G F h.1).toSTVertices := by rfl
    have := bottleneck_eq_flow p
    have := pos_bottleneck p G.source_not_sink
    grind
  grind

-- ============================================================
-- CONSTRUCTING THE MINIMUM CUT
-- ============================================================

/-- Extending a valid path u~>w by a fresh edge w→v yields a valid path u~>v.
  Requires v not already in the path (to preserve nodup). -/
lemma validuvPath.attachNode {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {G : FlowNetwork V α} {u w v : V}
    (p : validuvPath G u w) (hv : v ∉ p.verts.toFinset) (hedge : G.c w v > 0) :
    Nonempty (validuvPath G u v) := by
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
lemma validuvPath.prefix {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {G : FlowNetwork V α} {u w : V}
    (p : validuvPath G u w) {v : V} (hv : v ∈ p.verts.toFinset) :
    Nonempty (validuvPath G u v) := by
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

/-- If s can reach u in the residual and there is a residual edge u → v, then s can reach v. -/
lemma reach_extend {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {G : FlowNetwork V α} {F : RelaxedFlow V α G.toSTVertices} {h : ValidFlow V α G F} {u v : V}
    (hu : Nonempty (validuvPath (ResidualNetwork G F h) G.s u))
    (hedge : (ResidualNetwork G F h).c u v > 0) :
    Nonempty (validuvPath (ResidualNetwork G F h) G.s v) := by
  obtain ⟨p⟩ := hu
  by_cases hv : v ∈ p.verts.toFinset
  · exact p.prefix hv
  · exact p.attachNode hv hedge

/-- No augmenting path: t is not reachable from s via a valid path in the residual network. -/
def no_augmenting_path {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) : Prop :=
  ¬ Nonempty (augmentingPath (ResidualNetwork G F h))

open Classical in
/-- The set of vertices reachable from s via a valid path in the residual network. -/
noncomputable def mk_cut_set {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) : Finset V :=
  Finset.univ.filter (fun x => Nonempty (validuvPath (ResidualNetwork G F h) G.s x))

open Classical in
/-- Construct a cut from the reachable set when there is no augmenting path. -/
noncomputable def mk_cut_from_S {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F)
    (hno : no_augmenting_path G F h) : Cut V α G :=
  { S  := mk_cut_set G F h
    T  := Finset.univ \ mk_cut_set G F h
    hT := by ext a : 1; simp_all only [mem_sdiff, mem_univ, true_and]
    sins := by
      simp only [mk_cut_set, mem_filter, mem_univ, true_and]
      exact ⟨⟨[G.s], by simp, by simp, by simp, by simp⟩, fun i hi => by simp at hi⟩
    tint := by
      simp only [mem_sdiff, mem_univ, true_and, mk_cut_set, mem_filter]
      exact hno }

/-- Every forward arc from S to T is saturated. -/
lemma saturated_forward_arcs {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) :
    ∀ v w : V, v ∈ mk_cut_set G F h → w ∉ mk_cut_set G F h →
    F.f v w = G.c v w := by
  intro u v huS hvnS
  simp only [mk_cut_set, mem_filter, mem_univ, true_and] at huS hvnS
  apply le_antisymm (h u v)
  by_contra hlt
  push Not at hlt
  have hres : (ResidualNetwork G F h).c u v > 0 := by
    simp only [ResidualNetwork]; grind [F.nonneg_flow v u]
  exact hvnS (reach_extend huS hres)

/-- Every backward arc from T to S carries zero flow. -/
lemma zero_backward_arcs {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) :
    ∀ v w : V, v ∉ mk_cut_set G F h → w ∈ mk_cut_set G F h →
    F.f v w = 0 := by
  intro v w hvnS hwS
  by_contra hne
  simp only [mk_cut_set, mem_filter, mem_univ, true_and] at hwS hvnS
  have hpos : F.f v w > 0 := lt_of_le_of_ne (F.nonneg_flow v w) (Ne.symm hne)
  have hres : (ResidualNetwork G F h).c w v > 0 := by
    simp only [ResidualNetwork]; grind [F.nonneg_flow w v, h w v]
  exact hvnS (reach_extend hwS hres)

/-- When there is no augmenting path, the flow value equals the cut capacity. -/
lemma flow_eq_cut_cap {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F)
    (hno : no_augmenting_path G F h) :
    let C := mk_cut_from_S G F h hno
    Flow_value G.toSTVertices F = cut_cap C := by
  classical
  let C := mk_cut_from_S G F h hno
  rw [flow_value_eq_net_flow G C F]
  apply Finset.sum_congr rfl; intro v hv
  apply Finset.sum_congr rfl; intro w hw
  have hv' : v ∈ mk_cut_set G F h := hv
  have hw' : w ∉ mk_cut_set G F h := by simp_all only [mem_sdiff, mem_univ, true_and, C]; exact hw
  rw [zero_backward_arcs G F h w v hw' hv', sub_zero]
  exact saturated_forward_arcs G F h v w hv hw'

/-- If F is a max flow, there is no augmenting path. -/
lemma max_flow_no_augmenting_path {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] [DecidableEq V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : is_max_flow F) :
    no_augmenting_path G F h.1 :=
  fun ⟨p⟩ => max_flow_no_augmenting' F h p

-- ============================================================
-- MAX FLOW ATTAINED (ℤ)
-- ============================================================

open Classical in
/-- The S-T cut whose S consists of only the source -/
noncomputable
def sCut {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) : Cut V ℤ G where
  S := {G.s}
  T := univ \ {G.s}
  hT := rfl
  sins := by simp only [mem_singleton]
  tint := by grind [G.source_not_sink]

/-- For an integer flow network setting, there is a flow that attains the maximum flow -/
lemma max_flow_attained_Z {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) :
  ∃ F : RelaxedFlow V ℤ G.toSTVertices, is_max_flow F := by
    let B : ℤ := cut_cap (sCut G)
    have bound : ∀ F : RelaxedFlow V ℤ G.toSTVertices, ValidFlow V ℤ G F →
      Flow_value G.toSTVertices F ≤ B := by intro F val; exact weak_duality G (sCut G) F val
    have improv : ∀ F : RelaxedFlow V ℤ G.toSTVertices, ValidFlow V ℤ G F → ¬ is_max_flow F →
      ∃ F', ValidFlow V ℤ G F' ∧ Flow_value G.toSTVertices F' >= Flow_value G.toSTVertices F + 1 := by
      intro F val nmax
      dsimp [is_max_flow] at nmax
      simp only [val, true_and, not_forall, not_le] at nmax
      obtain ⟨F', ⟨val', lt⟩⟩ := nmax
      use F'
      refine ⟨val', lt⟩
    let F0 : RelaxedFlow V ℤ G.toSTVertices := trivial_flow G.toSTVertices
    have hF0 : ValidFlow V ℤ G F0 := valid_zero_flow G
    let P : ℕ → Prop := fun n =>
      ∃ F : RelaxedFlow V ℤ G.toSTVertices,
      ValidFlow V ℤ G F ∧
      Flow_value G.toSTVertices F ≥ n
    have hP0 : P 0 := by
      refine ⟨F0, hF0, ?_⟩
      simp [F0, zero_trivial_flow]
    have hstep :
      ∀ n : ℕ, P n →
        (∃ F : RelaxedFlow V ℤ G.toSTVertices, is_max_flow F) ∨ P (n + 1) := by
      intro n hn
      rcases hn with ⟨F, hvalid, hval⟩
      by_cases hmax : is_max_flow F
      · exact Or.inl ⟨F, hmax⟩
      · rcases improv F hvalid hmax with ⟨F', hvalid', himprov⟩
        right
        refine ⟨F', hvalid', ?_⟩
        have hnz : (n : ℤ) ≤ Flow_value G.toSTVertices F := by
          exact_mod_cast hval
        grind
    have hBnonneg : B ≥ 0 := by
      have := bound F0 hF0
      simp only [zero_trivial_flow, F0] at this
      exact this
    let N : ℕ := Int.toNat B + 1
    have : (∃ F : RelaxedFlow V ℤ G.toSTVertices, is_max_flow F) ∨ P N := by
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
          mk_out f {v} = mk_in f {v}) ∧
      (∀ u, f u G.s = 0) ∧
      (∀ u, f G.t u = 0) }

/-- Equivalent definition of the value of a flow without a flow structure -/
noncomputable
def flowValueFn {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) : (V → V → ℝ) → ℝ :=
  fun f => mk_out f {G.s}

/-- The set of functions that satisfy the capacity constraints -/
def capacityBox {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) : Set (V → V → ℝ) :=
  { f | ∀ u v, f u v ∈ Set.Icc (0 : ℝ) (G.c u v) }

/-- The set of feasible flows is a subset of
  the set of functions that satisfy the capacity constraints -/
lemma feasible_subset_box {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  FeasibleFlowSet G ⊆ capacityBox G := by
  intro f hf u v
  exact ⟨hf.1 u v, hf.2.1 u v⟩

/-- mk_out is continuous in perturbations of the input function -/
lemma continuous_mk_out {V : Type*} [Fintype V] (S : Finset V) :
  Continuous (fun f : V → V → ℝ => mk_out f S) := by
  simp [mk_out]
  continuity

/-- mk_in is continuous in perturbations of the input function -/
lemma continuous_mk_in {V : Type*} [Fintype V] (S : Finset V) :
  Continuous (fun f : V → V → ℝ => mk_in f S) := by
  simp [mk_in]
  continuity

/-- The value of a flow is continuous in perturbations of the flow -/
lemma continuous_flowValueFn {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  Continuous (flowValueFn G) := continuous_mk_out {G.s}

/-- The set of feasible flows is closed -/
lemma isClosed_feasibleFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  IsClosed (FeasibleFlowSet G) := by
  simp only [FeasibleFlowSet, ne_eq]
  have hnonneg : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
      isClosed_iInter (fun v => isClosed_le continuous_const (continuous_apply_apply u v))))
  have hcap : IsClosed {f : V → V → ℝ | ∀ u v, f u v ≤ G.c u v} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
      isClosed_iInter (fun v => isClosed_le (continuous_apply_apply u v) continuous_const)))
  have hcons : IsClosed {f : V → V → ℝ | ∀ v, v ≠ G.s → v ≠ G.t → mk_out f {v} = mk_in f {v}} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun v => isClosed_iInter (fun hs =>
       isClosed_iInter (fun ht => isClosed_eq (continuous_mk_out {v}) (continuous_mk_in {v})))))
  have hsource : IsClosed {f : V → V → ℝ | ∀ u, f u G.s = 0} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
        isClosed_eq (continuous_apply_apply u G.s) continuous_const))
  have hsink : IsClosed {f : V → V → ℝ | ∀ u, f G.t u = 0} := by
    simpa [Set.setOf_forall] using (isClosed_iInter (fun u =>
        isClosed_eq (continuous_apply_apply G.t u) continuous_const))
  exact hnonneg.inter (hcap.inter (hcons.inter (hsource.inter hsink)))

/-- The set of functions that satisfy capacity constraints is compact -/
lemma isCompact_capacityBox {V : Type*} [Fintype V]
  (G : FlowNetwork V ℝ) : IsCompact (capacityBox G) := by
  unfold capacityBox
  simp only [Set.mem_Icc]
  simpa [Set.pi, Set.iInter] using
    (isCompact_univ_pi fun u =>
      isCompact_univ_pi fun v =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (G.c u v))))

/-- The set of feasible functions is compact -/
lemma isCompact_feasibleFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  IsCompact (FeasibleFlowSet G) :=
  (isCompact_capacityBox G).of_isClosed_subset (isClosed_feasibleFlowSet G) (feasible_subset_box G)

/-- The set of feasible flows is nonempty -/
lemma feasibleFlowSet_nonempty {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  (FeasibleFlowSet G).Nonempty := by
  use ((trivial_flow G.toSTVertices).f)
  simp only [trivial_flow]
  rw [FeasibleFlowSet]
  simp only [ne_eq, mk_out, subset_univ, sum_sdiff_eq_sub, sum_singleton, sum_sub_distrib,
    mk_in, sub_left_inj, Set.mem_setOf_eq, Std.le_refl, implies_true, G.nonneg_capacity,
    sum_const_zero, and_self]

/-- For a flow network over reals setting, there is a flow that attains the maximum flow in the predicate setting-/
lemma max_flow_attained'_R {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  ∃ f ∈ FeasibleFlowSet G, ∀ g ∈ FeasibleFlowSet G, flowValueFn G g ≤ flowValueFn G f := by
  rcases (isCompact_feasibleFlowSet G).exists_isMaxOn (feasibleFlowSet_nonempty G)
    (continuous_flowValueFn G).continuousOn with ⟨f, hfF, hmax⟩
  use f, hfF
  intro _ hgF
  exact hmax hgF

/-- Any valid flow from the structure defintion is a feasible flow in the predicate definition -/
lemma flow_toFlowSet {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) (g : RelaxedFlow V ℝ G.toSTVertices)
  (gval : ValidFlow V ℝ G g) : g.f ∈ FeasibleFlowSet G := by
  rw [ValidFlow] at gval
  simp only [FeasibleFlowSet, ne_eq, Set.mem_setOf_eq, g.nonneg_flow, implies_true, gval,
    g.no_edges_in_source, g.no_edges_out_sink, and_self, and_true, true_and]
  intro v vngs vngt
  exact g.conservation v vngs vngt

/-- For a flow network over reals setting, there is a flow that attains the maximum flow -/
lemma max_flow_attained_R {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  ∃ F : RelaxedFlow V ℝ G.toSTVertices, is_max_flow F := by
    obtain ⟨g, gfeas, gopt⟩ := max_flow_attained'_R G
    rw [FeasibleFlowSet] at gfeas
    use ⟨g, by grind, by grind, by grind, by grind⟩
    rw [is_max_flow]
    constructor
    · grind [ValidFlow]
    · intro fn fnfeas
      have := gopt fn.f (flow_toFlowSet G fn fnfeas)
      rw [flowValueFn, flowValueFn] at this
      rw [Flow_value, Flow_value]
      simp only [ge_iff_le]
      exact this

-- ============================================================
-- MAX FLOW MIN CUT THEOREM
-- ============================================================

/-- The max-flow min-cut theorem: the maximum flow value equals the minimum cut capacity. -/
theorem max_flow_iff_eq_min_cut {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow V α G F) :
    is_max_flow F ↔
      ∃ C : Cut V α G, is_min_cut G C ∧ Flow_value G.toSTVertices F = cut_cap C := by
  constructor
  · -- forward
    intro hmax
    classical
    have hno : no_augmenting_path G F hmax.1 := fun ⟨p⟩ => max_flow_no_augmenting' F hmax p
    let C := mk_cut_from_S G F hmax.1 hno
    exact ⟨C, fun C' => by grind [flow_eq_cut_cap G F hmax.1 hno, weak_duality G C' F hmax.1],
              flow_eq_cut_cap G F hmax.1 hno⟩
  · --reverse
    rintro ⟨C, _, heq⟩
    exact max_flow_if_eq_cut G C F h heq

/-- Corollary: every maximum flow witnesses a minimum cut with equal value. -/
theorem max_flow_min_cut {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : is_max_flow F) :
    ∃ C : Cut V α G, is_min_cut G C ∧ Flow_value G.toSTVertices F = cut_cap C :=
  (max_flow_iff_eq_min_cut G F h.1).mp h

/-- Corollary: there exist a maximum flow and a minimum cut with equal value. -/
lemma max_flow_min_cut_R {V : Type*} [Fintype V] (G : FlowNetwork V ℝ) :
  ∃ (F : RelaxedFlow V ℝ G.toSTVertices), ∃ C : Cut V ℝ G,
  is_max_flow F ∧ is_min_cut G C ∧ Flow_value G.toSTVertices F = cut_cap C := by
    obtain ⟨F, hF⟩ := max_flow_attained_R G
    obtain ⟨C, hC⟩ := max_flow_min_cut G F hF
    use F, C

/-- Corollary: there exist a maximum flow and a minimum cut with equal value (ℤ version). -/
lemma max_flow_min_cut_Z {V : Type*} [Fintype V] (G : FlowNetwork V ℤ) :
  ∃ (F : RelaxedFlow V ℤ G.toSTVertices), ∃ C : Cut V ℤ G,
  is_max_flow F ∧ is_min_cut G C ∧ Flow_value G.toSTVertices F = cut_cap C := by
    obtain ⟨F, hF⟩ := max_flow_attained_Z G
    obtain ⟨C, hC⟩ := max_flow_min_cut G F hF
    use F, C

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
    (F : RelaxedFlow V ℤ G.toSTVertices) (h : ValidFlow V ℤ G.toFlowNetwork F) :
    is_max_flow (G := G.toFlowNetwork) F ↔
      ∃ C : Cut V ℤ G.toFlowNetwork, is_min_cut G.toFlowNetwork C ∧
        Flow_value G.toSTVertices F = cut_cap C :=
  max_flow_iff_eq_min_cut G.toFlowNetwork F h

-- ===========================================================
-- UNDIRECTED MAX FLOW MIN CUT THEOREM
-- ===========================================================

/-- Augmentation cancels out any 2-cycles: flow can't go both ways after augmentation -/
lemma no_bidirectional_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : STVertices V) :
  ∀ F F' : RelaxedFlow V α G, ∀ u v, (F * F').f u v = 0 ∨ (F * F').f v u = 0 := by
    intro F F' u v
    simp only [HMul.hMul, Mul.mul, sup_eq_right, tsub_le_iff_right, zero_add]
    have : F'.f v u + F.f v u = F.f v u + F'.f v u := by grind
    rw [this]
    have : F'.f u v + F.f u v = F.f u v + F'.f u v := by grind
    rw [this]
    exact le_total (F.f u v + F'.f u v) (F.f v u + F'.f v u)

/-- An undirected flow network can be modeled as a directed flow network
  where flow can only go in 1 direction -/
structure Undirected_FlowNetwork (V : Type*) [Fintype V] (α : Type*) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] extends FlowNetwork V α where
  c_symm : ∀ u v, c u v = c v u

/-- A valid undirected flow additionally requires that flow can only go in 1 direction:
  no 2-cycles are allowed -/
def ValidFlow_undirected (V : Type*) (α : Type*) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] (G : Undirected_FlowNetwork V α)
  (F : RelaxedFlow V α G.toSTVertices) : Prop :=
  (ValidFlow V α G.toFlowNetwork F) ∧ (∀ u v, F.f u v = 0 ∨ F.f v u = 0)

/-- An undirected flow is maximal if it's a valid undirected flow and its flow value is
  no less than any other valid undirected flow -/
def is_max_undirected_flow {V : Type*} {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [Fintype V] {G : Undirected_FlowNetwork V α}
    (fn : RelaxedFlow V α G.toSTVertices) : Prop :=
  ValidFlow_undirected V α G fn ∧ ∀ fn' : RelaxedFlow V α G.toSTVertices, ValidFlow_undirected V α G fn' →
    Flow_value G.toSTVertices fn' ≤ Flow_value G.toSTVertices fn

/-- Any undirected maximal flow is also a directed maximal flow -/
lemma undirected_max_directed_max {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α) (F : RelaxedFlow V α G.toSTVertices) :
  is_max_undirected_flow F → is_max_flow F := by
  intro h
  constructor
  · exact h.1.1
  · intro fn valfn
    have : Flow_value G.toSTVertices fn = Flow_value G.toSTVertices (fn * (trivial_flow G.toSTVertices)) := by simp [add_flow]
    rw [this]
    apply h.2
    constructor
    · exact valid_zero_augmentation G.toFlowNetwork _ valfn
    · exact no_bidirectional_flow G.toSTVertices fn (trivial_flow G.toSTVertices)

/-- The max-flow min-cut theorem: the maximum flow value equals the minimum cut capacity. -/
theorem undirected_max_flow_iff_eq_min_cut {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α)
    (F : RelaxedFlow V α G.toSTVertices) (h : ValidFlow_undirected V α G F) :
    is_max_undirected_flow F ↔
      ∃ C : Cut V α G.toFlowNetwork, is_min_cut G.toFlowNetwork C ∧ Flow_value G.toSTVertices F = cut_cap C := by
  constructor
  · -- forward
    intro h'
    have : is_max_flow F := undirected_max_directed_max G F h'
    obtain ⟨C, hC, FCeq⟩ := max_flow_min_cut G.toFlowNetwork F this
    use C
  · --reverse
    rintro ⟨C, mC, heq⟩
    constructor
    · exact h
    · intro fn valfn
      have := max_flow_iff_eq_min_cut G.toFlowNetwork F h.1
      have h' := this.mpr
      have : (∃ C, is_min_cut G.toFlowNetwork C ∧ Flow_value G.toSTVertices F = cut_cap C) := by use C
      have := h' this
      exact this.2 fn valfn.1

/-- every maximum flow witnesses a minimum cut with equal value -/
theorem undirected_max_flow_min_cut {V : Type*} [Fintype V] {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (G : Undirected_FlowNetwork V α)
  (F : RelaxedFlow V α G.toSTVertices) (h : is_max_undirected_flow F) :
    ∃ C, is_min_cut G.toFlowNetwork C ∧ Flow_value G.toSTVertices F = cut_cap C := (undirected_max_flow_iff_eq_min_cut G F h.1).mp h

/-- An equivalent for the max flow min cut theorem for ℤ for undirected flow networks -/
theorem undirected_max_flow_min_cut_Z {V : Type*} [Fintype V] (G : Undirected_FlowNetwork V ℤ) :
    ∃ F C, is_max_undirected_flow F ∧ is_min_cut G.toFlowNetwork C ∧
      Flow_value G.toSTVertices F = cut_cap C := by
      obtain ⟨F, C, hF, hC, FCeq⟩ := max_flow_min_cut_Z G.toFlowNetwork
      use F * (trivial_flow G.toSTVertices), C
      constructor
      · constructor
        · rw [ValidFlow_undirected]
          constructor
          · exact valid_zero_augmentation G.toFlowNetwork F hF.1
          · exact no_bidirectional_flow G.toSTVertices F (trivial_flow G.toSTVertices)
        · intro fn vfn;
          rw [is_max_flow] at hF
          simp [add_flow, hF.2 fn vfn.1]
      · constructor
        · exact hC
        · simp [add_flow, FCeq]

/-- An equivalent for the max flow min cut theorem for ℝ for undirected flow networks -/
theorem undirected_max_flow_min_cut_R {V : Type*} [Fintype V] (G : Undirected_FlowNetwork V ℝ) :
    ∃ F C, is_max_undirected_flow F ∧ is_min_cut G.toFlowNetwork C ∧
      Flow_value G.toSTVertices F = cut_cap C := by
      obtain ⟨F, C, hF, hC, FCeq⟩ := max_flow_min_cut_R G.toFlowNetwork
      use F * (trivial_flow G.toSTVertices), C
      constructor
      · constructor
        · rw [ValidFlow_undirected]
          constructor
          · exact valid_zero_augmentation G.toFlowNetwork F hF.1
          · exact no_bidirectional_flow G.toSTVertices F (trivial_flow G.toSTVertices)
        · intro fn vfn;
          rw [is_max_flow] at hF
          simp [add_flow, hF.2 fn vfn.1]
      · constructor
        · exact hC
        · simp [add_flow, FCeq]
