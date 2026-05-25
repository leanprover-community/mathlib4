/-
Copyright (c) 2026 Samuel Chassot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Chassot
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Existence of Eulerian trails

A connected finite graph has an Eulerian trail iff it has either zero or two
vertices of odd degree. This file proves the existence direction; the converse
is `SimpleGraph.Walk.IsEulerian.card_odd_degree` in
`Mathlib.Combinatorics.SimpleGraph.Trails`.

## Main results

* `SimpleGraph.Walk.exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two`:
  in a connected finite simple graph with zero or two odd-degree vertices,
  there exists an Eulerian trail.

## Implementation notes

The proof is the classical maximal-trail argument:
* a globally length-maximal trail exists by finite maximality;
* in the all-even case, such a trail must be closed and uses every edge;
* in the two-odd case, such a trail starts and ends at the two odd vertices,
  and a parity argument on a "maximal trail avoiding the chosen one" shows
  every edge is used.

The various "longest trail of some kind" constructions are unified through one
lemma `exists_maximal_walk`, parameterised by an arbitrary walk predicate.
-/

@[expose] public section

open scoped Sym2

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-! ### Trail extension lemmas -/

/-- Prepending an unused incident edge to a trail gives a strictly longer trail. -/
theorem IsTrail.exists_longer_of_unused_edge_at_start
    {u v w : V} {p : G.Walk v w} (hp : p.IsTrail)
    (huv : G.Adj u v) (hunused : s(u, v) ∉ p.edges) :
    ∃ q : G.Walk u w, q.IsTrail ∧ p.edges.length < q.edges.length :=
  ⟨cons huv p, hp.cons huv hunused, by simp⟩

/-- Helper: unpack a graph edge whose vertex set contains `v`. -/
private theorem exists_adj_of_mem_edgeSet_and_mem
    {v : V} {e : Sym2 V} (heG : e ∈ G.edgeSet) (hev : v ∈ e) :
    ∃ w, G.Adj v w ∧ e = s(v, w) := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mem_iff] at hev
    have hab : G.Adj a b := G.mem_edgeSet.mp heG
    rcases hev with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, Sym2.eq_swap⟩

/-! ### Bound trail length by the number of edges -/

section Fintype
variable [Fintype V] [DecidableRel G.Adj]

theorem IsTrail.length_edges_le_card_edgeFinset
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.edges.length ≤ G.edgeFinset.card := by
  classical
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := fun e he ↦ by
    rw [List.mem_toFinset] at he
    simpa using p.edges_subset_edgeSet he
  rw [← List.toFinset_card_of_nodup hp.edges_nodup]
  exact Finset.card_le_card hsub

end Fintype

/-! ### Existence of a length-maximal walk satisfying a predicate -/

section Finite
variable [Finite V]

/-- Existence of a walk of maximal edge-length among walks satisfying the predicate `P`.
Captures the common pattern behind every maximal-trail construction below. -/
private theorem exists_maximal_walk
    (P : ∀ ⦃x y : V⦄, G.Walk x y → Prop) (u₀ : V)
    (hnil : P (nil : G.Walk u₀ u₀))
    (hP_trail : ∀ ⦃x y⦄ (p : G.Walk x y), P p → p.IsTrail) :
    ∃ x y, ∃ p : G.Walk x y, P p ∧
      ∀ ⦃a b⦄ (q : G.Walk a b), P q → q.edges.length ≤ p.edges.length := by
  classical
  let _ := Fintype.ofFinite V
  set S : Finset ℕ := (Finset.range (G.edgeFinset.card + 1)).filter
    fun n => ∃ x y, ∃ p : G.Walk x y, P p ∧ p.edges.length = n with hS
  have h0 : 0 ∈ S :=
    Finset.mem_filter.mpr ⟨by simp, u₀, u₀, .nil, hnil, by simp⟩
  have hmem := Finset.mem_filter.mp (S.max'_mem ⟨0, h0⟩)
  obtain ⟨x, y, p, hpP, hpLen⟩ := hmem.2
  refine ⟨x, y, p, hpP, fun a b q hq => ?_⟩
  rw [hpLen]
  refine Finset.le_max' _ _ <| Finset.mem_filter.mpr ⟨?_, a, b, q, hq, rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le
    (hP_trail q hq).length_edges_le_card_edgeFinset)

end Finite

/-! ### Globally maximal trails -/

/-- A trail that is length-maximal among all trails in the graph. -/
def IsMaximalTrail {u v : V} (p : G.Walk u v) : Prop :=
  p.IsTrail ∧ ∀ ⦃x y⦄ (q : G.Walk x y), q.IsTrail →
    q.edges.length ≤ p.edges.length

namespace IsMaximalTrail

variable {u v : V} {p : G.Walk u v}

protected theorem isTrail (h : IsMaximalTrail p) : p.IsTrail := h.1

theorem length_le (h : IsMaximalTrail p) {x y : V} {q : G.Walk x y}
    (hq : q.IsTrail) : q.edges.length ≤ p.edges.length := h.2 q hq

/-- A maximal trail at its endpoint has used every incident edge. -/
theorem not_unused_edge_at_end (hpmax : IsMaximalTrail p) {w : V}
    (hvw : G.Adj v w) : s(v, w) ∈ p.edges := by
  by_contra hunused
  have hrev : p.reverse.IsTrail := hpmax.isTrail.reverse
  have hunusedRev : s(w, v) ∉ p.reverse.edges := by
    rw [edges_reverse, List.mem_reverse]
    simpa [Sym2.eq_swap] using hunused
  obtain ⟨q, hqT, hqL⟩ :=
    hrev.exists_longer_of_unused_edge_at_start hvw.symm hunusedRev
  have hle := hpmax.length_le hqT.reverse
  simp only [edges_reverse, List.length_reverse] at hle hqL
  omega

/-- The reverse of a maximal trail is maximal. -/
theorem reverse (hpmax : IsMaximalTrail p) : IsMaximalTrail p.reverse := by
  refine ⟨hpmax.isTrail.reverse, fun x y q hq => ?_⟩
  have := hpmax.length_le hq.reverse
  simpa [List.length_reverse] using this

end IsMaximalTrail

section Finite
variable [Finite V]

theorem exists_isMaximalTrail (u₀ : V) :
    ∃ x y, ∃ p : G.Walk x y, IsMaximalTrail p := by
  classical
  let _ := Fintype.ofFinite V
  exact exists_maximal_walk (P := fun _ _ p => p.IsTrail) u₀ (by simp)
    (fun _ _ _ h => h)

end Finite

/-! ### Degree counts at the endpoints of a trail -/

section DecEq
variable [DecidableEq V]

theorem IsTrail.odd_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (huv : u ≠ v) :
    Odd (p.edges.countP fun e => v ∈ e) := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  exact ((hp.even_countP_edges_iff v).mp hEven huv).2 rfl

end DecEq

section Fintype
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The edges of a maximal trail incident to its endpoint are precisely the
graph edges incident to that endpoint. -/
theorem IsMaximalTrail.filter_edgesFinset_eq_incidenceFinset
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) :
    hpmax.isTrail.edgesFinset.filter (fun e => v ∈ e) = G.incidenceFinset v := by
  ext e
  simp only [Finset.mem_filter, G.incidenceFinset_eq_filter, IsTrail.edgesFinset,
    Finset.mem_mk, Multiset.mem_coe]
  refine ⟨fun ⟨hep, hve⟩ => ⟨?_, hve⟩, fun ⟨heG, hve⟩ => ?_⟩
  · simpa using p.edges_subset_edgeSet hep
  · have heG' : e ∈ G.edgeSet := by simpa using heG
    rcases exists_adj_of_mem_edgeSet_and_mem (G := G) heG' hve with ⟨w, hvw, rfl⟩
    exact ⟨hpmax.not_unused_edge_at_end hvw, by simp⟩

/-- The number of trail edges incident to the endpoint of a maximal trail equals the
graph degree of that endpoint. -/
theorem IsMaximalTrail.countP_edges_right_eq_degree
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) :
    p.edges.countP (fun e => v ∈ e) = G.degree v := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter,
    ← G.card_incidenceFinset_eq_degree v]
  exact congrArg Finset.card hpmax.filter_edgesFinset_eq_incidenceFinset

omit [DecidableEq V] in
open scoped Classical in
/-- If a maximal trail has distinct endpoints, the final endpoint has odd degree. -/
theorem IsMaximalTrail.odd_degree_right_of_ne
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) (huv : u ≠ v) :
  Odd (G.degree v) :=
  hpmax.countP_edges_right_eq_degree ▸ hpmax.isTrail.odd_countP_edges_right_of_ne huv

omit [DecidableEq V] in
open scoped Classical in
/-- Symmetric version: starting vertex of a non-closed maximal trail has odd degree. -/
theorem IsMaximalTrail.odd_degree_left_of_ne
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) (huv : u ≠ v) :
  Odd (G.degree u) :=
  hpmax.reverse.odd_degree_right_of_ne huv.symm

omit [DecidableEq V] in
open scoped Classical in
/-- In an all-even graph, a maximal trail is closed. -/
theorem IsMaximalTrail.isClosed_of_forall_even_degree
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p)
    (heven : ∀ x : V, Even (G.degree x)) : u = v := by
  by_contra huv
  exact (Nat.not_even_iff_odd.mpr (hpmax.odd_degree_right_of_ne huv)) (heven v)

end Fintype

/-! ### Locating unused edges from connectedness -/

/-- Along a walk from inside the support of `p` to a vertex outside, there is a
first edge leaving `p.support`; that edge is incident to `p.support` and unused
by `p`. -/
private theorem exists_unused_incident_edge_of_walk_to_not_support
    {u v x y : V} {p : G.Walk u v} (w : G.Walk x y)
    (hx : x ∈ p.support) (hy : y ∉ p.support) :
    ∃ a b : V, a ∈ p.support ∧ G.Adj a b ∧ s(a, b) ∉ p.edges := by
  induction w with
  | nil => exact (hy hx).elim
  | cons hab tail ih =>
    by_cases hb : tail.getVert 0 ∈ p.support
    · exact ih (by simpa using hb) hy
    · refine ⟨_, _, hx, hab, fun hedge => hb ?_⟩
      exact p.mem_support_of_mem_edges hedge (by simp [Sym2.mem_iff])

/-- In a connected graph, an unused edge gives rise to an unused edge incident to
the support of `p`. -/
private theorem exists_unused_incident_edge_of_unused_edge
    {u v : V} {p : G.Walk u v} (hconn : G.Connected)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (hnot : e ∉ p.edges) :
    ∃ x y : V, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : G.Adj a b := G.mem_edgeSet.mp he
    by_cases ha : a ∈ p.support
    · exact ⟨a, b, ha, hab, by simpa using hnot⟩
    by_cases hb : b ∈ p.support
    · exact ⟨b, a, hb, hab.symm,
        fun hba => hnot (by simpa [Sym2.eq_swap] using hba)⟩
    obtain ⟨w⟩ := hconn.1 u a
    exact exists_unused_incident_edge_of_walk_to_not_support
      (p := p) w p.start_mem_support ha

/-! ### Closed maximal trails are Eulerian in connected graphs -/

section Fintype
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A closed globally maximal trail in a connected graph is Eulerian. -/
theorem IsMaximalTrail.isEulerian_of_connected_of_closed
    {u : V} {p : G.Walk u u} (hpmax : IsMaximalTrail p)
    (hconn : G.Connected) : p.IsEulerian := by
  refine hpmax.isTrail.isEulerian_of_forall_mem ?_
  intro e he
  by_contra hnot
  obtain ⟨x, y, hxp, hxy, hxy_not⟩ :=
    exists_unused_incident_edge_of_unused_edge (p := p) hconn he hnot
  let q : G.Walk x x := p.rotate x hxp
  have hqTrail : q.IsTrail :=
    (SimpleGraph.Walk.isTrail_rotate (c := p) hxp).mpr hpmax.isTrail
  have hxy_not_q : s(x, y) ∉ q.edges := fun hmem =>
    hxy_not ((p.rotate_edges x hxp).mem_iff.mp hmem)
  obtain ⟨r, hrTrail, hrLen⟩ :=
    hqTrail.exists_longer_of_unused_edge_at_start hxy.symm
      (by simpa [Sym2.eq_swap] using hxy_not_q)
  have hqLen : q.edges.length = p.edges.length :=
    (p.rotate_edges x hxp).perm.length_eq
  exact Nat.not_lt_of_ge (hpmax.length_le hrTrail) (hqLen ▸ hrLen)

/-- **Existence of an Eulerian walk** in a connected all-even-degree graph. -/
theorem exists_isEulerian_of_connected_forall_even_degree (u₀ : V)
    (hconn : G.Connected) (heven : ∀ x : V, Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  obtain ⟨x, y, p, hpmax⟩ := exists_isMaximalTrail (G := G) u₀
  have hxy : x = y := hpmax.isClosed_of_forall_even_degree heven
  subst y
  exact ⟨x, p, hpmax.isEulerian_of_connected_of_closed hconn⟩

/-! ### Two-odd-vertex case

The two-odd case needs a more delicate argument: a maximal trail has the two odd
vertices as endpoints (so it is not closed), and then a parity argument on a
"maximal trail avoiding `p`'s edges" shows there is no unused edge.
-/

omit [DecidableEq V] in
/-- If exactly two vertices have odd degree, any other vertex has even degree. -/
private theorem all_non_endpoint_even_of_card_odd_degree_eq_two
    {u v : V} (huv : u ≠ v)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2) :
    ∀ x : V, x ≠ u → x ≠ v → Even (G.degree x) := by
  classical
  intro x hxu hxv
  by_contra hxEven
  have hxOdd : Odd (G.degree x) := Nat.not_even_iff_odd.mp hxEven
  let U : {y : V | Odd (G.degree y)} := ⟨u, huOdd⟩
  let W : {y : V | Odd (G.degree y)} := ⟨v, hvOdd⟩
  let X : {y : V | Odd (G.degree y)} := ⟨x, hxOdd⟩
  have hUW : U ≠ W := fun h => huv (congrArg Subtype.val h)
  have hUX : U ≠ X := fun h => hxu (congrArg Subtype.val h).symm
  have hWX : W ≠ X := fun h => hxv (congrArg Subtype.val h).symm
  have h1 : U ∉ ({W, X} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hUW, hUX⟩
  have h2 : W ∉ ({X} : Finset _) := by
    simp only [Finset.mem_singleton]; exact hWX
  have h3 : ({U, W, X} : Finset _).card = 3 := by
    rw [show ({U, W, X} : Finset _) = insert U (insert W {X}) from rfl,
        Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_singleton]
  have hle := ({U, W, X} : Finset {y : V | Odd (G.degree y)}).card_le_univ
  omega

/-- A trail length-maximal among trails starting at `x` and avoiding `p.edges`. -/
def IsMaximalAvoidingFrom
    {u v x z : V} (p : G.Walk u v) (q : G.Walk x z) : Prop :=
  q.IsTrail ∧ q.edges.Disjoint p.edges ∧
    ∀ ⦃w⦄ (r : G.Walk x w), r.IsTrail → r.edges.Disjoint p.edges →
      r.edges.length ≤ q.edges.length

namespace IsMaximalAvoidingFrom

variable {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
protected theorem isTrail (h : IsMaximalAvoidingFrom p q) : q.IsTrail := h.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem disjoint (h : IsMaximalAvoidingFrom p q) : q.edges.Disjoint p.edges := h.2.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem length_le (h : IsMaximalAvoidingFrom p q) {w : V} {r : G.Walk x w}
    (hr : r.IsTrail) (hdisj : r.edges.Disjoint p.edges) :
    r.edges.length ≤ q.edges.length := h.2.2 r hr hdisj

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If `q` is maximal among trails from `x` avoiding `p.edges`, then any edge incident to
its endpoint that is also unused by `p` is already used by `q`. -/
theorem not_unused_edge_at_end (hqmax : IsMaximalAvoidingFrom p q)
    {w : V} (hyw : G.Adj z w) (hnotp : s(z, w) ∉ p.edges) :
    s(z, w) ∈ q.edges := by
  by_contra hnotq
  have hrev : q.reverse.IsTrail := hqmax.isTrail.reverse
  have hnotqRev : s(w, z) ∉ q.reverse.edges := by
    rw [edges_reverse, List.mem_reverse]
    simpa [Sym2.eq_swap] using hnotq
  let r : G.Walk x w := (cons hyw.symm q.reverse).reverse
  have hrTrail : r.IsTrail := (hrev.cons hyw.symm hnotqRev).reverse
  have hrDisj : r.edges.Disjoint p.edges := by
    intro e her hep
    rw [show r.edges = (cons hyw.symm q.reverse).edges.reverse from edges_reverse _,
      List.mem_reverse, edges_cons, List.mem_cons] at her
    rcases her with rfl | her'
    · exact hnotp (by simpa [Sym2.eq_swap] using hep)
    · rw [edges_reverse, List.mem_reverse] at her'
      exact hqmax.disjoint her' hep
  have hle := hqmax.length_le hrTrail hrDisj
  have hrLen : r.edges.length = q.edges.length + 1 := by simp [r, edges_cons]
  omega

end IsMaximalAvoidingFrom

section Finite
variable [Finite V]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Existence of a maximal trail avoiding the edges of a given walk. -/
private theorem exists_isMaximalAvoidingFrom {u v : V} (p : G.Walk u v) (x : V) :
    ∃ z, ∃ q : G.Walk x z, IsMaximalAvoidingFrom p q := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨a, z, q, hqP, hmax⟩ := exists_maximal_walk
    (P := fun ⦃a b⦄ (q : G.Walk a b) =>
      a = x ∧ q.IsTrail ∧ q.edges.Disjoint p.edges)
    x ⟨rfl, by simp, by simp⟩
    (fun _ _ _ h => h.2.1)
  obtain ⟨rfl, hqTrail, hqDisj⟩ := hqP
  exact ⟨z, q, hqTrail, hqDisj, fun w r hrTrail hrDisj =>
    hmax r ⟨rfl, hrTrail, hrDisj⟩⟩

end Finite

/-! ### Parity arguments for trails with two odd endpoints -/

/-- For a trail with the two odd-degree vertices as endpoints, the parity of the
edge-incidence count at `x` matches the parity of `G.degree x`. -/
private theorem IsTrail.even_countP_iff_even_degree_of_endpoints
    {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (huv : u ≠ v) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ z : V, z ≠ u → z ≠ v → Even (G.degree z)) :
    Even (p.edges.countP fun e => x ∈ e) ↔ Even (G.degree x) := by
  constructor
  · intro hEven
    by_cases hxu : x = u
    · subst hxu; exact ((hp.even_countP_edges_iff x).mp hEven huv).1 rfl |>.elim
    by_cases hxv : x = v
    · subst hxv; exact ((hp.even_countP_edges_iff x).mp hEven huv).2 rfl |>.elim
    exact hEvenAway x hxu hxv
  · intro hdegEven
    by_cases hxu : x = u
    · subst hxu; exact (Nat.not_even_iff_odd.mpr huOdd hdegEven).elim
    by_cases hxv : x = v
    · subst hxv; exact (Nat.not_even_iff_odd.mpr hvOdd hdegEven).elim
    exact (hp.even_countP_edges_iff x).mpr fun _ => ⟨hxu, hxv⟩

/-- Edges of a trail incident to a vertex `z`, viewed as a filter on `G.incidenceFinset z`. -/
private theorem IsTrail.filter_edgesFinset_eq_incidenceFinset_inter_used
    {u v z : V} {p : G.Walk u v} (hp : p.IsTrail) :
    hp.edgesFinset.filter (fun e => z ∈ e) =
      (G.incidenceFinset z).filter (fun e => e ∈ p.edges) := by
  ext e
  simp only [Finset.mem_filter, G.incidenceFinset_eq_filter, IsTrail.edgesFinset,
    Finset.mem_mk, Multiset.mem_coe]
  refine ⟨fun ⟨hep, hze⟩ => ⟨⟨?_, hze⟩, hep⟩, fun ⟨⟨_, hze⟩, hep⟩ => ⟨hep, hze⟩⟩
  simpa using p.edges_subset_edgeSet hep

/-- The "avoiding-from" analogue: for `q` maximal avoiding `p`, the edges of `q` incident to
its endpoint are precisely the incident-to-`z` edges not used by `p`. -/
private theorem IsMaximalAvoidingFrom.filter_edgesFinset_eq_incidenceFinset_inter_unused
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hqmax : IsMaximalAvoidingFrom p q) :
    hqmax.isTrail.edgesFinset.filter (fun e => z ∈ e) =
      (G.incidenceFinset z).filter (fun e => e ∉ p.edges) := by
  ext e
  simp only [Finset.mem_filter, G.incidenceFinset_eq_filter, IsTrail.edgesFinset,
    Finset.mem_mk, Multiset.mem_coe]
  refine ⟨fun ⟨heq, hze⟩ => ⟨⟨?_, hze⟩, fun hep => hqmax.disjoint heq hep⟩,
    fun ⟨⟨heG, hze⟩, hnotp⟩ => ?_⟩
  · simpa using q.edges_subset_edgeSet heq
  · have heG' : e ∈ G.edgeSet := by simpa using heG
    rcases exists_adj_of_mem_edgeSet_and_mem (G := G) heG' hze with ⟨w, hzw, rfl⟩
    exact ⟨hqmax.not_unused_edge_at_end hzw hnotp, by simp⟩

/-- A maximal trail avoiding `p.edges` (with `p` having two odd-degree endpoints)
has an *even* count of incident edges at its endpoint — so its endpoint matches its
start vertex. -/
private theorem IsMaximalAvoidingFrom.even_countP_edges_right_of_endpoints
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hp : p.IsTrail) (hqmax : IsMaximalAvoidingFrom p q)
    (huv : u ≠ v) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ t : V, t ≠ u → t ≠ v → Even (G.degree t)) :
    Even (q.edges.countP fun e => z ∈ e) := by
  set A : ℕ := ((G.incidenceFinset z).filter (fun e => e ∈ p.edges)).card
  set B : ℕ := ((G.incidenceFinset z).filter (fun e => e ∉ p.edges)).card
  set D : ℕ := (G.incidenceFinset z).card
  have hqCount : q.edges.countP (fun e => z ∈ e) = B := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    exact congrArg Finset.card hqmax.filter_edgesFinset_eq_incidenceFinset_inter_unused
  have hpCount : p.edges.countP (fun e => z ∈ e) = A := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    exact congrArg Finset.card hp.filter_edgesFinset_eq_incidenceFinset_inter_used
  have hpartition : A + B = D :=
    Finset.card_filter_add_card_filter_not (s := G.incidenceFinset z) _
  have hAD : Even A ↔ Even D := by
    have := hp.even_countP_iff_even_degree_of_endpoints (x := z)
      huv huOdd hvOdd hEvenAway
    rwa [hpCount, ← G.card_incidenceFinset_eq_degree z] at this
  rw [hqCount]
  rcases Nat.even_or_odd A with hA | hA
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨d, hd⟩ := hAD.mp ⟨a, ha⟩
    exact ⟨d - a, by omega⟩
  · have hAne : ¬ Even A := Nat.not_even_iff_odd.mpr hA
    have hDne : ¬ Even D := fun hDe => hAne (hAD.mpr hDe)
    obtain ⟨a, ha⟩ := hA
    obtain ⟨d, hd⟩ := Nat.not_even_iff_odd.mp hDne
    exact ⟨d - a, by omega⟩

omit [DecidableEq V] in
open scoped Classical in
/-- A maximal trail avoiding `p` (with `p` having two odd endpoints) is closed. -/
private theorem IsMaximalAvoidingFrom.isClosed_of_endpoints
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hp : p.IsTrail) (hqmax : IsMaximalAvoidingFrom p q)
    (huv : u ≠ v) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ t : V, t ≠ u → t ≠ v → Even (G.degree t)) :
    x = z := by
  by_contra hxz
  exact Nat.not_even_iff_odd.mpr (hqmax.isTrail.odd_countP_edges_right_of_ne hxz)
    (hqmax.even_countP_edges_right_of_endpoints hp huv huOdd hvOdd hEvenAway)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A maximal trail avoiding `p` has positive length if there is an unused incident edge
at its start vertex. -/
private theorem IsMaximalAvoidingFrom.length_pos_of_unused_adj_start
    {u v x y z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hqmax : IsMaximalAvoidingFrom p q)
    (hxy : G.Adj x y) (hxy_unused : s(x, y) ∉ p.edges) :
    0 < q.edges.length := by
  let r : G.Walk x y := cons hxy nil
  have hrTrail : r.IsTrail :=
    IsTrail.cons (w := (nil : G.Walk y y)) (by simp) hxy (by simp)
  have hrDisj : r.edges.Disjoint p.edges := by
    intro e her hep
    have heq : e = s(x, y) := by
      simpa [r] using her
    exact hxy_unused (heq ▸ hep)
  have hle := hqmax.length_le hrTrail hrDisj
  have hrLen : r.edges.length = 1 := by simp [r]
  omega

/-! ### Combining a closed detour with a maximal trail -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If a trail has a closed sub-trail starting at one of its support vertices, using
edges disjoint from the trail's, we can splice it in to get a strictly longer trail. -/
private theorem IsTrail.exists_longer_of_unused_closed_detour
    {u v x : V} {p : G.Walk u v} (hp : p.IsTrail) (hx : x ∈ p.support)
    {c : G.Walk x x} (hc : c.IsTrail)
    (hcNonempty : c.edges ≠ []) (hdisj : c.edges.Disjoint p.edges) :
    ∃ q : G.Walk u v, q.IsTrail ∧ p.edges.length < q.edges.length := by
  obtain ⟨p₁, p₂, hp_eq⟩ := mem_support_iff_exists_append.mp hx
  refine ⟨p₁.append (c.append p₂), ?_, ?_⟩
  · rw [isTrail_def]
    have hpNodup : (p₁.edges ++ p₂.edges).Nodup := by
      have := hp.edges_nodup; rwa [hp_eq, edges_append] at this
    obtain ⟨hp₁N, hp₂N, hp₁₂⟩ := List.nodup_append.mp hpNodup
    have hdisj₁₂ : c.edges.Disjoint (p₁.edges ++ p₂.edges) := by
      rwa [← edges_append, ← hp_eq]
    rw [edges_append, edges_append, List.nodup_append]
    refine ⟨hp₁N, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hc.edges_nodup, hp₂N, fun a hac _ hbp₂ hab => ?_⟩
      exact hdisj₁₂ hac (List.mem_append_right _ (hab ▸ hbp₂))
    · intro a hap₁ b hb hab
      rw [List.mem_append] at hb
      rcases hb with hbc | hbp₂
      · exact hdisj₁₂ (hab ▸ hbc) (List.mem_append_left _ hap₁)
      · exact hp₁₂ a hap₁ b hbp₂ hab
  · have hcLen : 0 < c.edges.length := by
      cases hce : c.edges with
      | nil => exact absurd hce hcNonempty
      | cons _ _ => simp
    have hpLen : p.edges.length = p₁.edges.length + p₂.edges.length := by
      rw [hp_eq, edges_append, List.length_append]
    rw [hpLen, edges_append, edges_append, List.length_append, List.length_append]
    omega

/-! ### Two-odd-vertex case: putting it together -/

omit [DecidableEq V] in
open scoped Classical in
/-- If a trail has an unused edge and there are exactly two odd-degree vertices, then
there is a closed detour from a support vertex using only unused edges. -/
private theorem exists_unused_closed_detour
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (hconn : G.Connected)
    (huv : u ≠ v) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (hnot : e ∉ p.edges) :
    ∃ x : V, ∃ c : G.Walk x x,
      x ∈ p.support ∧ c.IsTrail ∧ c.edges ≠ [] ∧ c.edges.Disjoint p.edges := by
  obtain ⟨x, y, hx, hxy, hxy_unused⟩ :=
    exists_unused_incident_edge_of_unused_edge (p := p) hconn he hnot
  have hEvenAway : ∀ z : V, z ≠ u → z ≠ v → Even (G.degree z) :=
    all_non_endpoint_even_of_card_odd_degree_eq_two huv huOdd hvOdd hodd
  obtain ⟨z, q, hqmax⟩ := exists_isMaximalAvoidingFrom p x
  have hpos : 0 < q.edges.length :=
    hqmax.length_pos_of_unused_adj_start hxy hxy_unused
  have hxz : x = z :=
    hqmax.isClosed_of_endpoints hp huv huOdd hvOdd hEvenAway
  subst z
  refine ⟨x, q, hx, hqmax.isTrail, ?_, hqmax.disjoint⟩
  intro hnil; rw [hnil] at hpos; simp at hpos

omit [DecidableEq V] in
open scoped Classical in
/-- In a connected graph with exactly two odd-degree vertices, a globally maximal trail
uses every edge. -/
private theorem IsMaximalTrail.mem_edges_of_connected_card_two
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) (hconn : G.Connected)
    (huv : u ≠ v) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2) :
    ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  intro e he
  by_contra hnot
  obtain ⟨x, c, hx, hc, hcNonempty, hdisj⟩ :=
    exists_unused_closed_detour hpmax.isTrail hconn huv huOdd hvOdd hodd he hnot
  obtain ⟨q, hqTrail, hqLong⟩ :=
    hpmax.isTrail.exists_longer_of_unused_closed_detour hx hc hcNonempty hdisj
  exact Nat.not_lt_of_ge (hpmax.length_le hqTrail) hqLong

omit [DecidableEq V] in
/-- Helper: if all degrees are even then there are no odd-degree vertices. -/
private theorem card_odd_degree_eq_zero_of_forall_even
    (heven : ∀ x : V, Even (G.degree x)) :
    Fintype.card {v : V | Odd (G.degree v)} = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun x => Nat.not_even_iff_odd.mpr x.2 (heven x)⟩

omit [DecidableEq V] in
open scoped Classical in
/-- In a connected graph with exactly two odd-degree vertices, a maximal trail is not
closed. -/
private theorem IsMaximalTrail.not_closed_of_card_odd_degree_eq_two
    {u v : V} {p : G.Walk u v} (hpmax : IsMaximalTrail p) (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 2) : u ≠ v := by
  intro huv
  subst v
  have hEuler : p.IsEulerian := hpmax.isEulerian_of_connected_of_closed hconn
  have hAllEven : ∀ x : V, Even (G.degree x) := fun x =>
    (hEuler.even_degree_iff (x := x)).mpr (fun h => (h rfl).elim)
  have := card_odd_degree_eq_zero_of_forall_even (G := G) hAllEven
  omega

/-- **Existence of an Eulerian walk** in a connected graph with exactly two odd-degree
vertices. -/
theorem exists_isEulerian_of_connected_card_oddDegree_eq_two
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 2) :
    ∃ u v, ∃ p : G.Walk u v, p.IsEulerian := by
  obtain ⟨u₀⟩ := hconn.nonempty
  obtain ⟨u, v, p, hpmax⟩ := exists_isMaximalTrail (G := G) u₀
  have huv := hpmax.not_closed_of_card_odd_degree_eq_two hconn hodd
  have huOdd := hpmax.odd_degree_left_of_ne huv
  have hvOdd := hpmax.odd_degree_right_of_ne huv
  refine ⟨u, v, p, hpmax.isTrail.isEulerian_of_forall_mem ?_⟩
  exact hpmax.mem_edges_of_connected_card_two hconn huv huOdd hvOdd hodd

omit [DecidableEq V] in
private theorem forall_even_degree_of_card_oddDegree_eq_zero
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 0) :
    ∀ v : V, Even (G.degree v) := by
  intro v
  by_contra hvEven
  have hvOdd : Odd (G.degree v) := Nat.not_even_iff_odd.mp hvEven
  exact (Fintype.card_eq_zero_iff.mp hodd).false ⟨v, hvOdd⟩

/-- **Main theorem.** A connected finite simple graph has an Eulerian walk iff it has
zero or two odd-degree vertices; this is the existence direction. -/
theorem exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 0 ∨
      Fintype.card {v : V | Odd (G.degree v)} = 2) :
    ∃ u v, ∃ p : G.Walk u v, p.IsEulerian := by
  rcases hodd with hzero | htwo
  · obtain ⟨u₀⟩ := hconn.nonempty
    have heven := forall_even_degree_of_card_oddDegree_eq_zero (G := G) hzero
    obtain ⟨u, p, hp⟩ :=
      exists_isEulerian_of_connected_forall_even_degree u₀ hconn heven
    exact ⟨u, u, p, hp⟩
  · exact exists_isEulerian_of_connected_card_oddDegree_eq_two hconn htwo

end Fintype
end Walk
end SimpleGraph
