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
import Mathlib.Data.Fintype.Prod

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
structure FlowNetwork (V : Type*) [Fintype V] extends STVertices V where
  c : V → V → ℝ
  nonneg_capacity : ∀ u v : V, c u v ≥ 0

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going into S -/
noncomputable
def mk_in {V : Type*} [Fintype V]
    (f : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ Finset.univ \ S, ∑ y ∈ S, f x y

open Classical in
/-- Given a function f and a set of vertices S, computes the sum over f applied to all edges
  (of the complete graph) going out of S -/
noncomputable
def mk_out {V : Type*} [Fintype V]
    (f : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, f x y

/-- A relaxedFlow is defined on a complete graph with source and sink and assigns to each edge
  a nonnegative flow value that satisfies flow conservation and does not send flow into the
  source or out of the sink. -/
structure RelaxedFlow (V : Type*) [Fintype V] (G : STVertices V) where
  f : V → V → ℝ
  nonneg_flow : ∀ u v : V, f u v ≥ 0
  conservation : ∀ v : V, v ≠ G.s → v ≠ G.t → mk_out f {v} = mk_in f {v}
  no_edges_in_source : ∀ u : V, f u G.s = 0
  no_edges_out_sink : ∀ u : V, f G.t u = 0

open Classical in
/-- An S-T cut partitions the set of vertices into a set S that
 contains the source and a set T that contains the sink. -/
structure Cut (V : Type*) [Fintype V] (G : FlowNetwork V) where
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
(V : Type*) [Fintype V] (G : FlowNetwork V) (g : RelaxedFlow V G.toSTVertices) : Prop :=
  ∀ u v : V, g.f u v ≤ G.c u v

/-- An (explicit) equivalent definition for flow conservation. -/
lemma eq_conservation (V : Type*) [Fintype V] (G : STVertices V) (flow : RelaxedFlow V G) :
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
instance (V : Type*) [Fintype V] (G : STVertices V) : Mul (RelaxedFlow V G) where
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
            simp [Finset.sum_add_distrib]; linarith
          _ = 0 := by
            simp only [add_eq_right, eq_conservation V G g v vns vnt,
              eq_conservation V G h v vns vnt];
      symm
      rw [←sub_eq_zero]
      have : ∀ x, -(g.f x v + h.f x v - g.f v x - h.f v x)
        = (g.f v x + h.f v x - g.f x v - h.f x v) := by
        intro x; ring
      simp only [this, sum_sub_distrib] at h₁
      exact h₁
    no_edges_in_source := by
      intro u;
      simp [g.no_edges_in_source, h.no_edges_in_source];
      linarith [g.nonneg_flow G.s u, h.nonneg_flow G.s u]
    no_edges_out_sink := by
      intro u; simp [g.no_edges_out_sink, h.no_edges_out_sink];
      linarith [g.nonneg_flow u G.t, h.nonneg_flow u G.t]
    }

/-- The value of a flow: the amount of flow going out of the sink. -/
noncomputable
def Flow_value {V : Type*} [Fintype V] (G : STVertices V)
    (flow : RelaxedFlow V G) : ℝ := mk_out flow.f {G.s}

/-- The value of a flow is nonnegative. -/
lemma nonneg_flow_value {V : Type*} [Fintype V] (G : STVertices V) :
  ∀F : RelaxedFlow V G, Flow_value G F ≥ 0 := by
  intro F; simp [Flow_value, mk_out, F.no_edges_in_source, sum_nonneg, F.nonneg_flow]

/-- The value of a flow is additive under augmentation. -/
lemma add_flow {V : Type*} [Fintype V] (G : STVertices V) (flow₁ flow₂ : RelaxedFlow V G) :
  Flow_value G (flow₁ * flow₂) = Flow_value G flow₁ + Flow_value G flow₂ := by
  have: ∀ x, (flow₁.f G.s x + flow₂.f G.s x) ≥ 0 := by
    intro x; linarith [flow₁.nonneg_flow G.s x, flow₂.nonneg_flow G.s x]
  simp [Flow_value, (· * ·), Mul.mul, mk_out,
   flow₁.no_edges_in_source, flow₂.no_edges_in_source, this, sum_add_distrib]

/-- The capacity of an S-T cut is the sum of edge capacities of edges going from S to T. -/
noncomputable
def cut_cap {V : Type*} [Fintype V] {G : FlowNetwork V}
    (c : Cut V G) : ℝ := mk_out G.c c.S

/-- The flow of an S-T cut given a RelaxedFlow is the sum of flows going over edges going
  from S to T. -/
noncomputable
def cut_flow {V : Type*} [Fintype V] {G : FlowNetwork V}
  (g : RelaxedFlow V G.toSTVertices)
    (c : Cut V G) : ℝ := mk_out g.f c.S

/-- A flow is maximal if it respects capacities and has the largest flow value compared to
 other flows that respect capacities. -/
def is_max_flow {V : Type*} [Fintype V] {G : FlowNetwork V}
    (fn : RelaxedFlow V G.toSTVertices) : Prop :=
  ValidFlow V G fn ∧ ∀ fn' : RelaxedFlow V G.toSTVertices, ValidFlow V G fn' →
    Flow_value G.toSTVertices fn' ≤ Flow_value G.toSTVertices fn

/-- A cut is minimal if its capapcity is minimal. -/
def is_min_cut {V : Type*} [Fintype V] (G : FlowNetwork V)
    (fn : Cut V G) : Prop :=
  ∀ fn' : Cut V G, cut_cap fn ≤ cut_cap fn'

/-- The residual network is a flow network defined using an existing flow network and flow.
  It uses the same source and sink. The capacity of an edge u v is given by its original capacity
  minus the amount of flow going over this edge plus the amount of flow going in the opposite
  direction. -/
def ResidualNetwork {V : Type*} [Fintype V] (G : FlowNetwork V) (F : RelaxedFlow V G.toSTVertices)
  (h : ValidFlow V G F) : FlowNetwork V where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c u v := G.c u v - F.f u v + F.f v u
  nonneg_capacity := by intro u v; rw [ge_iff_le]; linarith [h u v, F.nonneg_flow v u]

/-- Augmenting a valid flow in the original network with a valid flow in its residual network
  results in a new valid flow. -/
lemma valid_augmentation {V : Type*} [Fintype V] (G : FlowNetwork V)
  (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) :
  ∀F' : (RelaxedFlow V G.toSTVertices), ValidFlow V (ResidualNetwork G F h) F' →
  ∀ u v : V, (F * F').f u v ≤ G.c u v := by
  intro F' val_F' u v
  simp [(· * ·), Mul.mul]
  constructor
  · have : F'.f u v ≤ G.c u v - F.f u v + F.f v u := by exact val_F' u v
    linarith [F'.nonneg_flow v u, F.nonneg_flow u v]
  · linarith [G.nonneg_capacity u v]

/-- If a flow is maximal, all flows in its residual graph have value 0. -/
lemma max_flow_no_augmenting {V : Type*} [Fintype V] (G : FlowNetwork V)
  (F : RelaxedFlow V G.toSTVertices) (h : is_max_flow F) :
  ∀F' : (RelaxedFlow V G.toSTVertices), ValidFlow V (ResidualNetwork G F h.1) F' →
  Flow_value G.toSTVertices F' = 0 := by
  intro F' g
  by_contra con
  push Not at con
  have: Flow_value G.toSTVertices F' > 0 := by
   apply lt_of_le_of_ne;
   · linarith [nonneg_flow_value G.toSTVertices F']
   · symm; exact con
  let optF := F * F'
  have optge : Flow_value G.toSTVertices optF > Flow_value G.toSTVertices F := by calc
   Flow_value G.toSTVertices optF = Flow_value G.toSTVertices F + Flow_value G.toSTVertices F' :=
   by exact add_flow G.toSTVertices F F'
   _ > Flow_value G.toSTVertices F := by linarith
  have optval : ValidFlow V G optF := by
   apply valid_augmentation G F h.1 F' g
  have: ¬is_max_flow F := by
   simp only [is_max_flow, not_and, not_forall, not_le]; intro _; use optF;
  contradiction

-- ============================================================
-- WEAK DUALITY + OPTIMALITY CRITERION
-- ============================================================

/-- The flow of a cut is no more than the capacity of a cut. -/
lemma cut_flow_le_cut_cap {V : Type*} [Fintype V] (G : FlowNetwork V) (C : Cut V G)
  (g : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G g) :
  cut_flow g C ≤ cut_cap C := by
    simp only [cut_flow, cut_cap, mk_out]
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro w _
    exact h v w

open Classical in
/-- Flow conservation of the vertices in S without the source. -/
lemma helper {V : Type*} [Fintype V] (G : FlowNetwork V) (C : Cut V G)
  (g : RelaxedFlow V G.toSTVertices) :
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
    eq_conservation V G.toSTVertices g v vns vnt]

/-- You can add a singleton value in the sum. -/
lemma helper2 {V : Type*} [DecidableEq V] (S : Finset V) (a : V) (h : a ∈ S)
  (f : V → ℝ) : f a + ∑ b ∈ S \ {a}, f b = ∑ b ∈ S, f b := by
  refine add_eq_of_eq_sub ?_
  have : ∑ b ∈ S, f b - ∑ b ∈ S \ {a}, f b = f a := by simp [h]
  rw [this]

/-- If summing over a subset evaluates to 0, you can that subset from the original sum. -/
lemma helper3 {V : Type*} [DecidableEq V] (S : Finset V) (T : Finset V)
  (h : T ⊆ S) (f : V → ℝ) (h' : ∑ x ∈ T, f x = 0) : ∑ b ∈ S, f b = ∑ b ∈ S \ T, f b := by
  simp [h, h']

open Classical in
/-- For any cut, the value of a flow is equal to the sum of flows over edges from S to T
  minus the flow over edges from T to S. -/
lemma flow_value_eq_net_flow {V : Type*} [Fintype V]
    (G : FlowNetwork V) (C : Cut V G) (g : RelaxedFlow V G.toSTVertices) :
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
          rw [@helper2 V (Classical.decEq V) C.S G.s C.sins
            (fun v => ∑ w, (g.f v w - g.f w v))]
    _ = ∑ v ∈ C.S, ∑ w ∈ univ \ C.S, (g.f v w - g.f w v) := by
          rw [sum_comm]
          have htmp := @helper3 V (Classical.decEq V) univ C.S (subset_univ C.S)
            (fun v => ∑ w ∈ C.S, (g.f w v - g.f v w)) hinner
          rw [htmp, sum_comm]

/-- The value of a flow is no more than the flow of any cut. -/
lemma flow_le_cut_flow {V : Type*} [Fintype V]
    (G : FlowNetwork V) (C : Cut V G) (g : RelaxedFlow V G.toSTVertices) :
    Flow_value G.toSTVertices g ≤ cut_flow g C := by
  classical
  rw [flow_value_eq_net_flow G C g]
  simp only [cut_flow, mk_out]
  apply Finset.sum_le_sum; intro v _
  apply Finset.sum_le_sum; intro w _
  linarith [g.nonneg_flow w v]

/-- The value of a flow is no more than the capacity of any cut. -/
theorem weak_duality {V : Type*} [Fintype V] (G : FlowNetwork V) (C : Cut V G)
  (g : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G g) :
  Flow_value G.toSTVertices g ≤ cut_cap C := by
  linarith [cut_flow_le_cut_cap G C g h, flow_le_cut_flow G C g]

/-- If the value of a flow is equal to the capacity of any cut, the flow value is maximal. -/
lemma max_flow_if_eq_cut {V : Type*} [Fintype V] (G : FlowNetwork V) (C : Cut V G)
  (g : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G g) :
  Flow_value G.toSTVertices g = cut_cap C → is_max_flow g := by
    intro h'
    constructor
    · exact h
    · rw [h']
      apply weak_duality

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
structure validuvPath {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V) (u v : V)
  extends uvPath u v where
  valid : ∀ (i : ℕ) (h : i < verts.length - 1), G.c (verts[i]) (verts[i+1]) > 0

/-- An augmenting path is a valid path from s to t. -/
def augmentingPath {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V) :=
  validuvPath G G.s G.t

lemma ge_two_vertices {V : Type*} [Fintype V] {u v : V} (p : uvPath u v) (h : u ≠ v) :
 p.verts.length ≥ 2 := by
  grind [p.ustart, p.vend]

/-- The bottleneck capacity of a path: the minimum edge capacity along it. -/
def uvPath.bottleneck {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) {u v : V} (p : uvPath u v) (h : u ≠ v) : ℝ := by
    have : p.verts.length ≥ 2 := by apply ge_two_vertices p h
    have : p.verts.tail.length ≥ 1 := by grind
    let J := List.zipWith G.c p.verts p.verts.tail
    have : J.length ≥ 1 := by grind
    exact J.min (by grind)

lemma lb_bottleneck {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
  {u v : V} (p : uvPath u v) (h : u ≠ v) :
    ∀ (i : ℕ) (h' : i < p.verts.length - 1), p.bottleneck G h ≤ G.c p.verts[i] p.verts[i+1] := by
      intro i h'
      have : (p.verts[i], p.verts[i + 1]) = (List.zip p.verts p.verts.tail)[i]'(by grind) :=
        by grind
      have : G.c p.verts[i] p.verts[i+1] = (List.zipWith G.c p.verts p.verts.tail)[i]'(by grind) :=
        by grind
      grind [uvPath.bottleneck]

lemma ub_bottleneck {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V) {u v : V}
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
lemma pos_bottleneck {V : Type*} [Fintype V] [DecidableEq V]
  {G : FlowNetwork V} {u v : V} (p : validuvPath G u v) (h : u ≠ v) :
    p.touvPath.bottleneck G h > 0 := by
    obtain ⟨i, ⟨h', h''⟩⟩ := ub_bottleneck G p.touvPath h
    linarith [h'', lb_bottleneck G p.touvPath h i h', p.valid i h']


/-- The flow induced by an augmenting path: send bottleneck flow along each edge of the path. -/
def pathFlow {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V} (p : augmentingPath G) :
  V → V → ℝ := fun a b => if ∃ (i : ℕ) (h : i < p.verts.length - 1),
    a = p.verts[i] ∧ b = p.verts[i+1] then p.bottleneck G G.source_not_sink else 0

lemma neq_if_nodup {V : Type*} (l : List V) (i j : ℕ) (h₀ : i < l.length)
  (h₁ : j < l.length) (h₂ : i ≠ j) : l.Nodup → l[i] ≠ l[j] := by
  intro hnodup hEq
  apply h₂
  exact hnodup.getElem_inj_iff.mp hEq

lemma eq_index_if_nodup {V : Type*} (l : List V) (i j : ℕ) (h₀ : i < l.length)
    (h₁ : j < l.length) (h₂ : l[i] = l[j]) : l.Nodup → i = j := by
  intro hnodup
  exact (List.getElem_inj hnodup).mp h₂

lemma pathlike_flow_out {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
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

lemma pathlike_flow_in {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
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
def augmentingPath.toFlow {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (p : augmentingPath G) : RelaxedFlow V G.toSTVertices where
    f := pathFlow p
    nonneg_flow := by
      intro u v; rw [pathFlow]
      by_cases h : ∃ (i : ℕ) (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i+1]
      · simp [h]; linarith [pos_bottleneck p G.source_not_sink]
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
lemma bottleneck_eq_flow {V : Type*} [Fintype V] [DecidableEq V]
  {G : FlowNetwork V} (p : augmentingPath G) :
  p.bottleneck G G.source_not_sink = Flow_value G.toSTVertices p.toFlow := by
  rw [Flow_value]
  have : G.s = p.verts[0]'(by grind [p.ustart]) := by grind [p.ustart]
  rw [augmentingPath.toFlow]
  simp_all only
  have := pathlike_flow_out p 0 (by grind [p.ustart, p.vend, G.source_not_sink])
  rw [this]

/-- The flow induced by an augmenting path is valid. -/
lemma augmentingPath.valid_toFlow {V : Type*} [Fintype V] [DecidableEq V]
  {G : FlowNetwork V} (p : augmentingPath G) : ValidFlow V G p.toFlow := by
  simp only [ValidFlow, toFlow, pathFlow]
  intro u v
  by_cases h : ∃ i, ∃ (h : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i + 1]
  · simp only [h, ↓reduceIte]
    obtain ⟨i, ⟨h, ⟨rfl, rfl⟩⟩⟩ := h
    exact lb_bottleneck G p.touvPath G.source_not_sink i h
  · simp only [h, ↓reduceIte]; exact G.nonneg_capacity u v

/-- If F is a max flow, there is no augmenting path in its residual network. -/
lemma max_flow_no_augmenting' {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (F : RelaxedFlow V G.toSTVertices) (h : is_max_flow F) :
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
  linarith

-- ============================================================
-- CONSTRUCTING THE MINIMUM CUT
-- ============================================================

/-- Extending a valid path u~>w by a fresh edge w->v yields a valid path u~>v.
  Requires v not already in the path (to preserve nodup). -/
lemma validuvPath.attachNode {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V} {u w v : V}
    (p : validuvPath G u w) (hv : v ∉ p.verts.toFinset) (hedge : G.c w v > 0) :
    Nonempty (validuvPath G u v) := by
  let newverts := p.verts ++ [v]
  refine ⟨⟨⟨newverts, ?nonempty, ?nodup, ?ustart, ?vend⟩, ?valid⟩⟩
  · -- non-empty
    exact List.concat_ne_nil v p.verts
  · -- nodub
    simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self, List.mem_cons, or_false, ne_eq, forall_eq, true_and, newverts]
    rw [List.mem_toFinset] at hv
    constructor
    · -- original list was nodup
      exact p.nodup
    · -- no element in the original list equals v
      exact fun a a_1 ↦ ne_of_mem_of_not_mem a_1 hv
  · -- old head stays old head
    grind only [= List.head_append_of_ne_nil, p.ustart]
  · -- new element becomes new last
    exact List.getLast_concat
  · -- is valid, i.e. every consectutive pair still has postive capacity
    intro i
    by_cases h' : i < p.verts.length - 1
    · grind only [= List.getElem_append, p.valid]
    · grind [p.vend]

/-- Given a path u~>w and a vertex v already on the path, extract the prefix path u~>v. -/
lemma validuvPath.prefix {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V} {u w : V}
    (p : validuvPath G u w) {v : V} (hv : v ∈ p.verts.toFinset) :
    Nonempty (validuvPath G u v) := by
  rw [List.mem_toFinset] at hv
  obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hv
  refine ⟨⟨⟨p.verts.take (i + 1), ?_, p.nodup.take, ?_, ?_⟩, ?_⟩⟩
  · -- non-empty
    simp only [ne_eq, List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or];
    exact p.nonempty
  · -- head
    simp [List.head_take, p.ustart]
  · -- last
    rw [List.getLast_take]; simp_all only [add_tsub_cancel_right, getElem?_pos, Option.getD_some]
  · -- valid
    intro j hj
    have hj' : j < p.verts.length - 1 := by simp [List.length_take] at hj; omega
    simp only [List.getElem_take, gt_iff_lt]; exact p.valid j hj'

/-- If s can reach u in the residual and there is a residual edge u -> v, then s can reach v. -/
lemma reach_extend {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {F : RelaxedFlow V G.toSTVertices} {h : ValidFlow V G F} {u v : V}
    (hu : Nonempty (validuvPath (ResidualNetwork G F h) G.s u))
    (hedge : (ResidualNetwork G F h).c u v > 0) :
    Nonempty (validuvPath (ResidualNetwork G F h) G.s v) := by
  obtain ⟨p⟩ := hu
  by_cases hv : v ∈ p.verts.toFinset
  · exact p.prefix hv
  · exact p.attachNode hv hedge

/-- No augmenting path: t is not reachable from s via a valid path in the residual network. -/
def no_augmenting_path {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) : Prop :=
  ¬ Nonempty (augmentingPath (ResidualNetwork G F h))

open Classical in
/-- The set of vertices reachable from s via a valid path in the residual network. -/
noncomputable def mk_cut_set {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) : Finset V :=
  Finset.univ.filter (fun x => Nonempty (validuvPath (ResidualNetwork G F h) G.s x))

open Classical in
/-- Construct a cut from the reachable set when there is no augmenting path. -/
noncomputable def mk_cut_from_S {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F)
    (hno : no_augmenting_path G F h) : Cut V G :=
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
lemma saturated_forward_arcs {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) :
    ∀ v w : V, v ∈ mk_cut_set G F h → w ∉ mk_cut_set G F h →
    F.f v w = G.c v w := by
  intro u v huS hvnS
  simp only [mk_cut_set, mem_filter, mem_univ, true_and] at huS hvnS
  apply le_antisymm (h u v)
  by_contra hlt
  push Not at hlt
  have hres : (ResidualNetwork G F h).c u v > 0 := by
    simp only [ResidualNetwork]; linarith [F.nonneg_flow v u]
  exact hvnS (reach_extend huS hres)

/-- Every backward arc from T to S carries zero flow. -/
lemma zero_backward_arcs {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) :
    ∀ v w : V, v ∉ mk_cut_set G F h → w ∈ mk_cut_set G F h →
    F.f v w = 0 := by
  intro v w hvnS hwS
  by_contra hne
  simp only [mk_cut_set, mem_filter, mem_univ, true_and] at hwS hvnS
  have hpos : F.f v w > 0 := lt_of_le_of_ne (F.nonneg_flow v w) (Ne.symm hne)
  have hres : (ResidualNetwork G F h).c w v > 0 := by
    simp only [ResidualNetwork]; linarith [F.nonneg_flow w v, h w v]
  exact hvnS (reach_extend hwS hres)

/-- When there is no augmenting path, the flow value equals the cut capacity. -/
lemma flow_eq_cut_cap {V : Type*} [Fintype V] [DecidableEq V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F)
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

-- ============================================================
-- MAX FLOW MIN CUT THEOREM
-- ============================================================

/-- The max-flow min-cut theorem: the maximum flow value equals the minimum cut capacity. -/
theorem max_flow_iff_eq_min_cut {V : Type*} [Fintype V] (G : FlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) :
    is_max_flow F ↔
      ∃ C : Cut V G, is_min_cut G C ∧ Flow_value G.toSTVertices F = cut_cap C := by
  constructor
  · -- forward
    intro hmax
    classical
    have hno : no_augmenting_path G F hmax.1 := fun ⟨p⟩ => max_flow_no_augmenting' F hmax p
    let C := mk_cut_from_S G F hmax.1 hno
    exact ⟨C, fun C' => by linarith [flow_eq_cut_cap G F hmax.1 hno, weak_duality G C' F hmax.1],
              flow_eq_cut_cap G F hmax.1 hno⟩
  · --reverse
    rintro ⟨C, _, heq⟩
    exact max_flow_if_eq_cut G C F h heq

-- ============================================================
-- MAX FLOW MIN CUT THEOREM (natural numbers edition)
-- ============================================================

structure NatFlowNetwork (V : Type*) [Fintype V] extends STVertices V where
  c : V → V → ℕ

def NatFlowNetwork.toFlowNetwork {V : Type*} [Fintype V]
    (G : NatFlowNetwork V) : FlowNetwork V where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c := fun u v => (G.c u v : ℝ)
  nonneg_capacity := by
    norm_num

theorem max_flow_iff_eq_min_cut_N {V : Type*} [Fintype V] (G : NatFlowNetwork V)
    (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G.toFlowNetwork F) :
    is_max_flow (G := G.toFlowNetwork) F ↔
      ∃ C : Cut V G.toFlowNetwork, is_min_cut G.toFlowNetwork C ∧
        Flow_value G.toSTVertices F = cut_cap C := by
  exact max_flow_iff_eq_min_cut G.toFlowNetwork F h

-- ============================================================
-- VERTEX CAPCACITY
-- ============================================================

structure FlowNetworkVertex (V : Type*) [Fintype V] extends FlowNetwork V where
vc : V → ℝ
vc_nonneg : ∀ u, vc u ≥ 0

/-- A ValidFlow is a relaxedFlow that also satisfies capacity constraints which are
  defined in a FlowNetwork. -/
def ValidVertexFlow
(V : Type*) [Fintype V] (G : FlowNetworkVertex V) (g : RelaxedFlow V G.toSTVertices) : Prop :=
  ValidFlow V G.toFlowNetwork g ∧ ∀ u : V, mk_in g.f {u} ≤ G.vc u

/-- just a simple set with two elements to indicate whether a node is an in or an out
   node. I could have used booleans (which already has nice properties like finiteness and norm_num)
   it would be confusing what True and False meant in that case -/
inductive NodeSide | In | Out
  deriving DecidableEq, Repr

-- For some reason, lean did not see that a set of two elements is finite :(
instance : Fintype NodeSide where
  elems := ⟨[NodeSide.In, NodeSide.Out], by decide⟩
  complete := fun x => by cases x <;> decide

-- This is so that things like norm_num work, just like boolens
@[simp] lemma NodeSide.in_ne_out : NodeSide.In ≠ NodeSide.Out := by decide
@[simp] lemma NodeSide.out_ne_in : NodeSide.Out ≠ NodeSide.In := by decide

open NodeSide in
/-- Ordinary flow network derived from vertex capacity network -/
@[simp]
def ExpandedFlowNetworkVertex (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V) :
    FlowNetwork (V × NodeSide) where
    -- Canonical source: In vertex of the real source
  s := (G.s, In)
  -- Canonical sink: Out veterx of real sink
  t := (G.t, Out)
  -- This would be really ugly if we didn't define in_ne_out
  source_not_sink := by norm_num
  c := fun x y =>
    match x, y with
    | (u, In), (v, Out) =>
        if h : u = v then G.vc u else 0
    | (u, Out), (v, In) =>
        if v = G.s then 0
        else if u = G.t then 0
        else G.c u v
    | _, _ =>
        0
  nonneg_capacity := by
    intro x y
    rcases x with ⟨u, bu⟩
    rcases y with ⟨v, bv⟩
    -- split by each In/Out case
    -- In/In and Out/Out are trivial
    -- In/Out is because vc is nonneg
    -- Out/In because regular edge capacities
    cases bu <;> cases bv
    · grind
    · grind [G.vc_nonneg u]
    · grind [G.nonneg_capacity u v]
    · gcongr


open NodeSide in
/-- Flow into an Out vertex is the same has the flow into an In vertex -/
lemma flow_in_out_eq_flow_in_in
    (V : Type*) [DecidableEq V] [Fintype V]
    (G : FlowNetworkVertex V)
    (g : RelaxedFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G) g)
    (u : V) :
    g.f (u, In) (u, Out) = ∑ x, g.f (u, In) x := by
  have h1 := hg (u, Out) (u, Out)
  have h2 := hg (u, In) (u, In)
  have hzero : ∀ (a b : V × NodeSide),
    (ExpandedFlowNetworkVertex V G).c a b = 0 → g.f a b = 0 := by
      intro a b hc
      have hle := hg a b
      linarith [hg a b, g.nonneg_flow a b]
  have hzeroin : ∀ (v : V) (b : NodeSide), (v, b) ≠ (u, In) →
      g.f (v, b) (u, Out) = 0 := by
    intro v b hvb
    apply hzero
    simp only [ExpandedFlowNetworkVertex]
    rcases b with _ | _
    · simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Std.le_refl, Prod.forall,
      Prod.mk.injEq, and_true, ↓reduceDIte]
    · simp
  have lhs : ∑ x, g.f x (u, Out) = g.f (u, In) (u, Out) :=
  Finset.sum_eq_single (u, In)
    (fun ⟨v, b⟩ _ hvb => hzeroin v b (by grind))
    (by simp)
  have hzeroout : ∀ (v : V) (b : NodeSide), (v, b) ≠ (u, Out) →
      g.f (u, In) (v, b)  = 0 := by
    intro v b hvb
    apply hzero
    simp only [ExpandedFlowNetworkVertex]
    rcases b with _ | _
    · simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Std.le_refl, Prod.forall,
      Prod.mk.injEq, not_and]
    · exact dif_neg fun a ↦ hvb (congrFun (congrArg Prod.mk (id (Eq.symm a))) Out)
  have rhs : ∑ x, g.f (u, In) x = g.f (u, In) (u, Out) :=
  Finset.sum_eq_single (u, Out)
    (fun ⟨v, b⟩ _ hvb => hzeroout v b (by grind))
    (by simp)
  simp_all

open NodeSide in
/-- Given a flow on the expanded network, recover the corresponding flow on the original
  FlowNetworkVertex by reading off the flow on edges (u, Out) -> (v, In), which correspond
  to the original edges u -> v.

  We have to use ValidFlow on the expanded graph here because otherwise conservation may not hold -/
def ContractedFlow (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V)
    (g : RelaxedFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G) g) :
    RelaxedFlow V G.toSTVertices where
  f u v := g.f (u, Out) (v, In)
  nonneg_flow := fun u v => g.nonneg_flow (u, Out) (v, In)
  conservation := by
    intro v vns vnt
    have hIn  := g.conservation (v, NodeSide.In)
      (by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.mk.injEq, and_true,
        not_false_eq_true] )
      (by simp  [ExpandedFlowNetworkVertex, vnt])
    have hOut := g.conservation (v, NodeSide.Out)
      (by simp [ExpandedFlowNetworkVertex, vns])
      (by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.mk.injEq, and_true,
        not_false_eq_true])
    -- zero capacity implies zero flow
    have hzero : ∀ (a b : V × NodeSide),
    (ExpandedFlowNetworkVertex V G).c a b = 0 → g.f a b = 0 := by
      intro a b hc
      linarith [hg a b, g.nonneg_flow a b]
    -- I am not proud of this code, but it works :)
    have hzeroout : ∀ (w : V) (b : NodeSide), (w, b) ≠ (v, In) →
    g.f (w, b) (v, Out) = 0 := by
      aesop
    simp only [mk_out, ExpandedFlowNetworkVertex, dite_eq_ite, subset_univ, sum_sdiff_eq_sub,
      sum_singleton, sum_sub_distrib, mk_in, sub_left_inj] at hIn hOut
    simp only [mk_out, mk_in, Finset.sum_singleton]
    have hzOut : ∀ x : V, g.f (v, Out) (x, Out) = 0 := fun x =>
      hzero (v, Out) (x, Out) (by simp)
    have hzIn : ∀ x : V, g.f (x, In) (v, In) = 0 := fun x =>
      hzero (x, In) (v, In) (by simp)
    have NodeSide_sum_out :
    ∀ x : V, ∑ b : NodeSide, g.f (v, Out) (x, b) = g.f (v, Out) (x, In) := by
      intro x; have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
      simp only [this, ExpandedFlowNetworkVertex, dite_eq_ite, Finset.sum_pair NodeSide.in_ne_out,
        hzOut, add_zero]
    have NodeSide_sum_in : ∀ x : V, ∑ b : NodeSide, g.f (x, b) (v, In) = g.f (x, Out) (v, In) := by
      intro x; have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
      simp [this, Finset.sum_pair NodeSide.in_ne_out, hzIn]
    have lhs_collapse : ∑ x : V × NodeSide, g.f (v, Out) x = ∑ x : V, g.f (v, Out) (x, In) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]; simp [NodeSide_sum_out]
    have rhs_collapse : ∑ x : V × NodeSide, g.f x (v, In) = ∑ x : V, g.f (x, Out) (v, In) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]; simp [NodeSide_sum_in]
    have mid : ∑ x : V × NodeSide, g.f (v, Out) x = ∑ x : V × NodeSide, g.f x (v, In) := by
      have hA : ∑ x : V × NodeSide, g.f (v, In) x = g.f (v, In) (v, Out) :=
        (flow_in_out_eq_flow_in_in V G g hg v).symm
      have hB : ∑ x : V × NodeSide, g.f x (v, Out) = g.f (v, In) (v, Out) :=
        Finset.sum_eq_single (f := fun x => g.f x (v, Out)) (v, In)
          (fun p _ hp => by obtain ⟨w, b⟩ := p; exact hzeroout w b hp) (by simp)
      linarith [hIn, hOut, hA, hB]
    have total_eq : ∑ x : V, g.f (v, Out) (x, In) = ∑ x : V, g.f (x, Out) (v, In) := by
      linarith [lhs_collapse, rhs_collapse, mid]
    have split : ∀ (f : V → ℝ), ∑ x : V, f x = f v + ∑ x ∈ Finset.univ \ {v}, f x := fun f => by
      rw [← Finset.sum_sdiff (Finset.subset_univ {v})]; simp
    have s1 : ∑ x : V, g.f (v, Out) (x, In) =
        g.f (v, Out) (v, In) + ∑ x ∈ Finset.univ \ {v}, g.f (v, Out) (x, In) := split _
    have s2 : ∑ x : V, g.f (x, Out) (v, In) =
        g.f (v, Out) (v, In) + ∑ x ∈ Finset.univ \ {v}, g.f (x, Out) (v, In) := split _
    have total_eq' :
        ∑ x ∈ Finset.univ \ {v}, g.f (v, Out) (x, In) =
          ∑ x ∈ Finset.univ \ {v}, g.f (x, Out) (v, In) := by
      linarith [total_eq, s1, s2]
    clear hzOut hzIn NodeSide_sum_out NodeSide_sum_in
      lhs_collapse rhs_collapse mid total_eq split s1 s2
    simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, ne_eq, Prod.forall, Prod.mk.injEq,
      not_and, subset_univ, sum_sdiff_eq_sub, sum_singleton, sub_left_inj]
  no_edges_in_source := by
    intro u
    apply le_antisymm _ (g.nonneg_flow (u, Out) (G.s, In))
    have key := hg (u, Out) (G.s, In)
    simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte] at key
    exact key
  no_edges_out_sink := by
    intro u
    apply le_antisymm _ (g.nonneg_flow (G.t, Out) (u, In))
    have key := hg (G.t, Out) (u, In)
    simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte, ite_self] at key
    exact key


open NodeSide in
theorem FlowInducesValidVertexFlow (V : Type*) [DecidableEq V] [Fintype V] (G : FlowNetworkVertex V)
    (g : RelaxedFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G).toSTVertices)
    (hg : ValidFlow (V × NodeSide) (ExpandedFlowNetworkVertex V G) g) :
    ValidVertexFlow V G (ContractedFlow V G g hg) := by
  constructor
  · intro u v
    have hcg := hg (u, Out) (v, In)
    have h1 := hg (u, Out) (v, In)
    simp only [ContractedFlow, ExpandedFlowNetworkVertex] at *
    split_ifs at h1 <;> linarith [G.nonneg_capacity u v, g.nonneg_flow (u, Out) (v, In)]
  · intro u
    by_cases h : u = G.s
    · simp_all only [mk_in, ContractedFlow, ExpandedFlowNetworkVertex, dite_eq_ite, sum_singleton,
      subset_univ, sum_sdiff_eq_sub, tsub_le_iff_right]
      have hs0 : ∀ vs : (V × NodeSide), g.f vs (u, In) = 0 := by
          intro vs
          have hcg := hg vs (u, In)
          apply le_antisymm
          · aesop
          · exact g.nonneg_flow vs (u, In)
      have rhs : ∑ x, g.f (x, Out) (G.s, In) = 0 :=
        by simp_all only [ExpandedFlowNetworkVertex, dite_eq_ite, Prod.forall, sum_const_zero]
      rw [rhs]
      linarith [g.nonneg_flow (G.s, Out) (G.s, In), G.vc_nonneg G.s]
    · push Not at h
      simp only [mk_in, ContractedFlow, ExpandedFlowNetworkVertex, dite_eq_ite, sum_singleton,
        subset_univ, sum_sdiff_eq_sub, tsub_le_iff_right]
      have key     := g.conservation (u, In) (by simp [h]) (by simp)
      have hInOut  := hg (u, In) (u, Out)
      simp only [ExpandedFlowNetworkVertex, dite_eq_ite, ↓reduceIte] at hInOut
      -- conservation: mk_out {(u,In)} = mk_in {(u,In)}, unfold to get the sum equation
      have hcons : ∑ x, g.f x (u, In) = ∑ x, g.f (u, In) x := by
        simp only [mk_out, mk_in, Finset.sum_singleton, subset_univ, sum_sdiff_eq_sub] at key
        linarith
      -- flow_in_out_eq_flow_in_in: g.f (u,In) (u,Out) = ∑ x, g.f (u,In) x
      have hfio := flow_in_out_eq_flow_in_in V G g hg u
      have h3 : ∑ x, g.f (x, Out) (u, In) ≤ ∑ x, g.f x (u, In) := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        apply Finset.sum_le_sum; intro x _
        have : (Finset.univ : Finset NodeSide) = {In, Out} := by decide
        simp only [this, Finset.sum_pair NodeSide.in_ne_out]
        linarith [g.nonneg_flow (x, In) (u, In)]
      -- chain: ∑(x,Out)->(u,In) ≤ ∑ x->(u,In) = ∑ (u,In)->x = (u,In)->(u,Out) ≤ vc u
      linarith [g.nonneg_flow (u, Out) (u, In)]
