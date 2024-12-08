/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Dynamics.FixedPoints.Increasing
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Bondy-Chvátal theorem

In this file we proved Bondy-Chvátal theorem and some of its corollaries.

## Main theorems

* `SimpleGraph.IsHamiltonian.from_closure`: Bondy-Chvátal theorem, a graph is
  Hamiltonian iff its closure is Hamiltonian.
* `SimpleGraph.IsHamiltonian.dirac_theorem`: Dirac's theorem: If `G` is a graph with
  at least 3 vertices, and deg(u) ≥ |V| / 2 for every vertex `u`, then `G` is Hamiltonian.
* `SimpleGraph.IsHamiltonian.ore_theorem`: Ore's theorem: If `G` is a graph with
  at least 3 vertices, and deg(u) + deg(v) ≥ |V| for every non-adjacent vertices `u` and `v`,
  then `G` is Hamiltonian.
-/

namespace SimpleGraph

open Classical Walk Function
open scoped List
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

local notation "‖" X "‖" => Fintype.card X

/-- The set of possible new edges that can be added in the next step. -/
def closureNewEdges :=
  { (u, v) : V × V | G.degree u + G.degree v ≥ ‖V‖ ∧ u ≠ v ∧ ¬G.Adj u v }

/-- One single step for building the closure. -/
noncomputable def closureStep : SimpleGraph V :=
  if h : (closureNewEdges G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G

lemma self_le_closureStep : G ≤ closureStep G := by
  unfold closureStep
  split_ifs with h
  repeat simp

/-- The closure of a graph, obtained by repeatedly adding an edge `(u, v)`
  where `deg(u) + deg(v) ≥ n`. -/
noncomputable def closure := Function.eventualValue self_le_closureStep G

lemma closureStep_diff_atmost_one : (closureStep G \ G).edgeSet.Subsingleton := by
  unfold closureStep
  split_ifs with h
  · simp only [sup_sdiff_left_self, edgeSet_sdiff]
    apply Set.Subsingleton.anti (t := (edge h.some.1 h.some.2).edgeSet)
    · have : h.some.1 ≠ h.some.2 := h.some_mem.2.1
      simp [edge_edgeSet_of_ne (this)]
    · apply Set.diff_subset
  · simp

lemma closureStep_deleteEdge {u v : V} (huv : ¬G.Adj u v) (huv' : G.closureStep.Adj u v) :
    G.closureStep.deleteEdges {s(u, v)} = G := by
  rw [← edgeSet_inj]
  ext e
  simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
  apply Iff.intro
  · rintro ⟨he₁, he₂⟩
    by_contra he₃
    have mem₁ : e ∈ (closureStep G \ G).edgeSet := by simpa using ⟨he₁, he₃⟩
    have mem₂ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simpa using ⟨huv', huv⟩
    exact he₂ <| (closureStep_diff_atmost_one G) mem₁ mem₂
  · intro he
    apply And.intro (edgeSet_mono (self_le_closureStep G) he)
    intro he'
    simp only [he', mem_edgeSet] at he
    exact huv he

lemma closureStep_eq_iff' : closureStep G = G ↔ closureNewEdges G = ∅ := by
  unfold closureStep
  split_ifs with h
  · have : (G ⊔ edge h.some.1 h.some.2 = G) ↔ False := by
      simp only [sup_eq_left, ← isSubgraph_eq_le, IsSubgraph, iff_false, not_forall]
      use h.some.1, h.some.2
      simpa [edge_adj] using h.some_mem.2
    simp only [this, false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h

lemma closureStep_eq_iff : closureStep G = G ↔
    ∀ {u} {v}, u ≠ v → G.degree u + G.degree v ≥ ‖V‖ → G.Adj u v := by
  simp only [closureStep_eq_iff', closureNewEdges,
    Set.eq_empty_iff_forall_not_mem, Set.mem_setOf, Prod.forall]
  apply forall₂_congr
  intros
  tauto

lemma closureStep_deg_sum {u v : V} (huv : ¬G.Adj u v) (huv' : G.closureStep.Adj u v) :
    G.degree u + G.degree v ≥ ‖V‖ := by
  have ne : (closureNewEdges G).Nonempty := by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty, ← closureStep_eq_iff', Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w := ne.some
  have prop₁ : G.degree w.1 + G.degree w.2 ≥ ‖V‖ := ne.some_mem.1
  have mem₁ : s(u, v) ∈ (closureStep G \ G).edgeSet := by simpa using ⟨huv', huv⟩
  have mem₂ : s(w.1, w.2) ∈ (closureStep G \ G).edgeSet := by
    have prop₂ : w.1 ≠ w.2 := ne.some_mem.2.1
    have prop₃ : ¬G.Adj w.1 w.2 := ne.some_mem.2.2
    have G_eq : G.closureStep = G ⊔ edge w.1 w.2 := by simp[closureStep, ne]
    simpa [-Prod.mk.eta, G_eq, edge_adj] using And.intro prop₂ prop₃
  have edge_eq := (closureStep_diff_atmost_one G mem₁ mem₂).symm
  simp only [Prod.mk.eta, Sym2.eq, Sym2.rel_iff'] at edge_eq
  cases' edge_eq with h h
  · rw [h] at prop₁
    simpa using prop₁
  · rw [h] at prop₁
    rw [add_comm]
    simpa using prop₁

lemma self_le_closure : G ≤ closure G := by
  rw [closure]
  apply Function.self_le_eventualValue

lemma closure_spec : ∀ {u} {v}, u ≠ v →
    G.closure.degree u + G.closure.degree v ≥ ‖V‖ → G.closure.Adj u v := by
  have : closureStep (closure G) = closure G := isFixedPt_eventualValue self_le_closureStep G
  rwa [closureStep_eq_iff] at this

variable {G}

private theorem from_ClosureStep_aux
    {u u' v v' : V} {p : G.Walk u u'}
    (hV : ‖V‖ ≥ 3) (hp : p.support ~ Finset.univ.toList)
    (ne : v ≠ u') (vu' : G.Adj v u') (v'u : G.Adj v' u)
    (d : G.Dart) (hd : d ∈ p.darts) (hd₁ : d.fst = v) (hd₂ : d.snd = v') :
    IsHamiltonian G := by
  have hv : v ∈ p.support := by simp [List.Perm.mem_iff hp]
  have not_nil : ¬(p.dropUntil v hv).Nil := dropUntil_not_nil hv ne
  have snd_eq_v' : (p.dropUntil v hv).getVert 1 = v' := by
    rw [← hd₂]
    refine p.next_unique ?_
      (p.darts_dropUntil_subset _ <| (p.dropUntil v hv).firstDart_mem_darts not_nil)
      hd (by simp [hd₁])
    have : p.support.Nodup := by
      rw [List.Perm.nodup_iff hp]
      apply Finset.nodup_toList
    apply List.Nodup.sublist (List.dropLast_sublist _) this
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ => ⟨u, q, this⟩
  apply IsHamiltonianCycle.isHamiltonianCycle_of_tail_toFinset
  · have := p.sum_takeUntil_dropUntil_length hv
    have := calc
      p.length + 1 = p.support.length := by simp
      _ = Finset.univ.toList.length := by apply List.Perm.length_eq hp
      _ = ‖V‖ := by simp
    have := Walk.length_tail_add_one not_nil
    simp [q, add_assoc]
    omega
  · assumption
  · simp only [tail_support_append, support_cons, support_nil, List.tail_cons, support_copy,
      support_reverse, List.tails_reverse, List.append_assoc, List.singleton_append,
      List.cons_append, List.toFinset_append, List.toFinset_cons, List.toFinset_reverse,
      List.toFinset_nil, insert_emptyc_eq, Finset.union_insert, Finset.eq_univ_iff_forall,
      Finset.mem_insert, Finset.mem_union, List.mem_toFinset, Finset.mem_singleton,
      Finset.not_mem_empty, false_or, q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁, hw₂, hw₃, hw₄⟩
    have mem_tail : w ∈ p.support.tail := by
      have mem : w ∈ p.support := by simp [List.Perm.mem_iff hp]
      rw [Walk.support_eq_cons] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop : w ∉ (p.dropUntil v hv).support.tail := by
      have tail_not_nil := support_tail_ne_nil not_nil
      have : (p.dropUntil v hv).support.tail.getLast tail_not_nil = u' := by
        rw [List.getLast_tail, getLast_support]
      rw [← List.dropLast_append_getLast tail_not_nil, this]
      rw [List.tail_reverse_eq_reverse_dropLast, List.mem_reverse] at hw₃
      simpa [← support_tail_of_not_nil _ not_nil] using ⟨hw₃, hw₁⟩
    have append : p.support.tail =
        (p.takeUntil v hv).support.tail ++ (p.dropUntil v hv).support.tail := by
      rw [← tail_support_append, take_spec]
    simp only [append, List.mem_append] at mem_tail
    cases' mem_tail with h h
    exact hw₂ h
    exact not_mem_drop h

private theorem from_ClosureStep_aux'
    {u v : V} {q : G.closureStep.Walk u u} (hq : q.IsHamiltonianCycle) (hV : ‖V‖ ≥ 3)
    (huv : G.degree u + G.degree v ≥ ‖V‖) (hv : v = hq.next u) (not_adj : ¬G.Adj u v) :
    ∃ w w' d, G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst = w' ∧ d.snd = w := by
  let X := (hq.next ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.next v}
  have cardX : G.degree u - 1 ≤ X.toFinset.card := calc
    _ = (G.neighborFinset u).card - 1 := by simp
    _ = (Finset.univ.filter (G.Adj u)).card - 1 := by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.next ·)).card - ({u} : Finset _).card := by
      simp [Finset.card_image_of_injective _ hq.next_inj]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.next ·)) \ {u}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [X]
  have cardY : G.degree v - 1 ≤ Y.toFinset.card := calc
    _ = (G.neighborFinset v).card - 1 := by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card - ({hq.next v} : Finset _).card := by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.next v}).card := by
      apply Finset.le_card_sdiff
    _ = _ := by simp [Y]
  have card_union : (X ∪ Y).toFinset.card ≤ ‖V‖ - 3 := calc
    _ ≤ ({v, hq.next v, u}ᶜ : Finset _).card := by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq, Set.toFinset_union,
        Set.toFinset_diff, Set.toFinset_image, Set.toFinset_setOf, Set.toFinset_singleton,
        Finset.compl_union, Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and, not_and, Decidable.not_not,
        forall_exists_index, and_imp, X, Y] at hw ⊢
      apply And.intro
      · intro w' adj next
        rcases hw with hw | hw | hw
        · rw [hw, hv] at next
          rw [hq.next_inj next] at adj
          simp at adj
        · rw [hw] at next
          rw [hq.next_inj next] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _ = _ := by
      suffices ({v, hq.next v, u} : Finset _).card = 3 by rw [Finset.card_compl, this]
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem]
      · simp
      · simpa [hv] using hq.next_next_ne
      · simpa [hv] using And.intro hq.next_ne.symm hq.next_ne
  have non_empty : (X ∩ Y).toFinset.card ≠ 0 := fun h => by
    suffices ‖V‖ - 2 ≤ ‖V‖ - 3 by omega
    calc
      _ ≤ (G.degree u + G.degree v) - 2 := Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u - 1) + (G.degree v - 1) := by omega
      _ ≤ X.toFinset.card + Y.toFinset.card := add_le_add cardX cardY
      _ = (X ∪ Y).toFinset.card + (X ∩ Y).toFinset.card := by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ ‖V‖ - 3 + 0 := add_le_add card_union (le_of_eq h)
      _ = ‖V‖ - 3 := by simp
  obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp non_empty
  simp only [Set.mem_setOf_eq, Set.toFinset_inter, Set.toFinset_diff, Set.toFinset_image,
    Set.toFinset_setOf, Set.toFinset_singleton, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    X, Y] at hw
  rcases hw with ⟨⟨⟨w', hw'₁, hw'₂⟩, -⟩, hw₂, -⟩
  obtain ⟨d, hd₁, hd₂⟩ := hq.self_next_in_darts w'
  rw [hw'₂] at hd₂
  exact ⟨w, w', d, hw₂.symm, hw'₁.symm, hd₁, hd₂⟩

theorem from_ClosureStep (hG : IsHamiltonian (closureStep G)) : IsHamiltonian G := by
  by_cases trivial : Fintype.card V = 1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a, p, hp⟩ := hG trivial
    obtain ⟨d, hd, hd'⟩ : ∃ d ∈ p.darts, ¬G.Adj d.fst d.snd := by
      by_contra h
      simp only [not_exists, not_and, Decidable.not_not] at h
      have edgeSubset (e) (he : e ∈ p.edges) : e ∈ G.edgeSet := by
        simp only [edges, List.mem_map] at he
        obtain ⟨d, hd, hd'⟩ := he
        rw [← hd']
        exact h _ hd
      let q := p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ => ⟨a, q, this⟩)
      exact hp.transfer edgeSubset
    set u := d.fst
    set v := d.snd
    have hu : u ∈ p.support := Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q := p.rotate hu
    have hq : q.IsHamiltonianCycle := hp.rotate u
    have hd_q : d ∈ q.darts := by
      simpa [q] using List.IsRotated.mem_iff (rotate_darts _ _) |>.mpr hd
    have q_not_nil : ¬q.Nil := by
      erw [rotate_Nil_iff]
      exact hp.1.not_nil
    have next_u_eq_v : q.getVert 1 = v := by
      exact hq.1.next_unique (q.firstDart_mem_darts q_not_nil) hd_q rfl
    have uv_not_edge : s(u, v) ∉ q.tail.edges := by
      have : q = cons (q.adj_getVert_one q_not_nil) q.tail := by
        exact (q.cons_tail_eq q_not_nil).symm
      have : q.edges = s(u, v) :: q.tail.edges := by
        simp only [this, edges_cons]
        simpa using Or.inl next_u_eq_v
      intro h
      have nodup := hq.1.edges_nodup
      rw [this] at nodup
      exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del : G.closureStep.deleteEdges {s(u, v)} = G := by
      exact closureStep_deleteEdge _ hd' d.adj
    let q' := q.tail
      |>.toDeleteEdge s(u, v) uv_not_edge
      |>.transfer G (by
        simp (config := {singlePass := true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q' : q'.support ~ Finset.univ.toList := by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer, support_copy, support_transfer, support_tail,
        List.perm_iff_count, hq.2, q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [← support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV : ‖V‖ ≥ 3 := hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum := closureStep_deg_sum G hd' d.adj
    have next_u : v = hq.next u := by
      obtain ⟨d', hd'₁, hd'₂, hd'₃⟩ := hq.self_next_in_darts u
      exact hd'₃ ▸ hq.isCycle.next_unique hd_q hd'₁ hd'₂.symm
    obtain ⟨w, w', d', hw, hw', d'_mem, hd'₁, hd'₂⟩ :=
      from_ClosureStep_aux' hq hV deg_sum next_u hd'
    have q'_support : q'.support = q.support.tail := by
      simp [q', support_tail_of_not_nil _ q_not_nil]
    obtain ⟨i, i_lt, hi⟩ := List.getElem_of_mem d'_mem
    simp only [length_darts] at i_lt
    rw [← hi, darts_getElem_snd i i_lt] at hd'₂
    rw [← hi, darts_getElem_fst i i_lt] at hd'₁
    have i_nz : i ≠ 0 := by
      intro i_zero
      simp only [i_zero, List.getElem_zero, head_support] at hd'₁
      simp [hd'₁] at hw'
    have i_min_1 : i - 1 < q'.darts.length := by
      have q'_length : q'.length = q.length - 1 := by
        have := length_tail_add_one q_not_nil
        simp [transfer_transfer, length_copy, length_transfer, q']
        omega
      simp [q'_length]
      omega
    have hd''₁ : (q'.darts[i - 1]).fst = w' := by
      rw [darts_getElem_fst _ (by simpa using i_min_1)]
      simp only [q'_support, ← List.drop_one]
      rw [List.getElem_drop, ← hd'₁]
      congr 1
      omega
    have hd''₂ : (q'.darts[i - 1]).snd = w := by
      rw [darts_getElem_snd _ (by simpa using i_min_1)]
      simp only [q'_support, ← List.drop_one]
      rw [List.getElem_drop, ← hd'₂]
      congr 1
      omega
    have w'_ne_u : w' ≠ u := fun eq => by simp [eq] at hw'
    have Hamiltonian :=
      from_ClosureStep_aux hV perm_q' w'_ne_u hw' hw q'.darts[i - 1]
      (List.getElem_mem _ _ _) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian

private theorem from_closure_aux {n} (hG : ¬IsHamiltonian G) :
    ¬IsHamiltonian (closureStep^[n] G) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply, iterate_one, Decidable.not_not] at ih ⊢
    exact from_ClosureStep ih

theorem from_closure_iff : IsHamiltonian (closure G) ↔ IsHamiltonian G := by
  apply Iff.intro <;> intro hG
  · unfold closure Function.eventualValue at hG
    contrapose hG
    exact from_closure_aux hG
  · exact IsHamiltonian.mono (self_le_closure _) hG

theorem dirac_theorem (hV : ‖V‖ ≥ 3) (hG : ∀ u, 2 * G.degree u ≥ ‖V‖) : G.IsHamiltonian := by
  suffices G.closure = (⊤ : SimpleGraph V) from
    from_closure_iff.mp (this ▸ IsHamiltonian.complete_graph (by omega))
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj, ne_eq] at ne
  apply closure_spec G ne
  calc
    ‖V‖ ≤ G.degree u + G.degree v := by
      have := hG u
      have := hG v
      omega
    _ ≤ G.closure.degree u + G.closure.degree v :=
      add_le_add (degree_mono (self_le_closure G)) (degree_mono (self_le_closure G))

theorem ore_theorem (hV : ‖V‖ ≥ 3) (hG : ∀ {u} {v}, ¬G.Adj u v → G.degree u + G.degree v ≥ ‖V‖) :
    G.IsHamiltonian := by
  suffices G.closure = (⊤ : SimpleGraph V) from
    from_closure_iff.mp (this ▸ IsHamiltonian.complete_graph (by omega))
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj, ne_eq] at ne
  by_cases adj : G.Adj u v
  · exact self_le_closure G adj
  · apply closure_spec G ne
    calc
      ‖V‖ ≤ G.degree u + G.degree v := hG adj
      _ ≤ G.closure.degree u + G.closure.degree v :=
        add_le_add (degree_mono (self_le_closure G)) (degree_mono (self_le_closure G))

end SimpleGraph
