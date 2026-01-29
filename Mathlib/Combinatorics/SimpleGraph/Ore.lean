/-
Copyright (c) 2026 Shao Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shao Yu
-/



module


public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.GetD




/-!

# Simple graphs

We proved Ore's theorem in graph theory:
  Let G be a graph of order n ≥ 3 that satisfies the Ore property, then G has a Hamilton cycle.

## Main definitions

* `Walk.IsMaximalPath` is the definiton of a simple path of fixed maximum length between two points..

* `Walk.IsMaxlongPath` is the definiton of the longest simple path in a graph.

-/
@[expose] public section

open SimpleGraph Finset Walk Function List




variable {V : Type*} {e : Sym2 V}


/--
Define a simple path of fixed maximum length between two points.
-/
def Walk.IsMaximalPath {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ (q : G.Walk a b), q.IsPath → q.length ≤ p.length


/--
Defines the longest simple path in a graph.
-/
def Walk.IsMaxlongPath {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ (c d : V), ∀ (q : G.Walk c d),  q.IsPath → q.length ≤ p.length



/--
Between any two points, there must exist a longest path.
-/
lemma exists_maximal_path [Fintype V] {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected) :
  ∀ (a b : V), ∃ (p : G.Walk a b), Walk.IsMaximalPath p := by
  intro a b
  by_cases h : a ≠ b
  · let S : ℕ → Set (G.Walk a b) := fun (n : ℕ) => {(p : G.Walk a b) | p.IsPath ∧ p.length = n}
    let lengths := {n |∃ (p : G.Walk a b), p.IsPath ∧ p.length = n}
    classical
    obtain H := SimpleGraph.fintypeSetPathLength G a b
    have lengths_Finite : lengths.Finite := by
      have bound : ∀ n ∈ lengths, n ≤ Fintype.card V := by
        intro n hn
        rcases hn with ⟨p, hp, rfl⟩
        have h_card : p.support.length ≤ Fintype.card V := by
          exact List.Nodup.length_le_card hp.support_nodup
        simp_all only [ne_eq, SimpleGraph.Walk.length_support, ge_iff_le]
        omega
      have finite_bounded : Set.Finite {n : ℕ | n ≤ Fintype.card V} := by
        obtain H := Set.finite_le_nat (n := Fintype.card V)
        simp_all only [ne_eq]
      exact Set.Finite.subset finite_bounded bound
    have lengths_Nonempty : lengths.Nonempty := by
      rw [Set.nonempty_def]
      have : ∃ (q : G.Walk a b), q.IsPath := by
        exact SimpleGraph.Connected.exists_isPath hG a b
      rcases this with ⟨q, hq⟩
      refine ⟨q.length, q, hq, rfl⟩
    obtain maximal := Set.Finite.exists_maximal (h := lengths_Finite) (hs := lengths_Nonempty)
    rcases maximal with ⟨i, hi⟩
    simp_all only [ne_eq]
    unfold Walk.IsMaximalPath
    rw [maximal_mem_iff] at hi
    have : ∃ (p : G.Walk a b) , p.length = i ∧  p ∈ S i := by
      rcases hi with ⟨hi_mem, hi_max⟩
      unfold lengths at hi_mem
      simp_rw [Set.mem_setOf_eq] at hi_mem
      rcases hi_mem with ⟨p, hp_is_path, hp_length⟩
      refine ⟨p, hp_length, ?_⟩
      unfold S
      simp only [Set.mem_setOf_eq, hp_is_path, hp_length, and_self]
    rcases this with ⟨p, hp⟩
    use p
    constructor
    · simp only [Set.mem_setOf_eq, S] at hp
      rcases hp with ⟨h1, h2, h3⟩
      exact h2
    · simp_all only
      intro q hq
      have : q.length ∈ lengths := by
        unfold lengths
        refine ⟨q, hq, rfl⟩
      rcases hi with ⟨h1,h2⟩
      obtain := h2 this
      simp_all only [ge_iff_le]
      omega
  · unfold Walk.IsMaximalPath
    have h_eq : a = b := by simp_all only [ne_eq, not_not]
    subst h_eq
    use SimpleGraph.Walk.nil
    constructor
    · simp_all only [SimpleGraph.Walk.isPath_iff_eq_nil]
    · intro q hq
      simp_all only [SimpleGraph.Walk.isPath_iff_eq_nil, le_refl]



/--
In a connected graph, there must exist a path of maximum length.
-/
lemma exists_maxilongmal_path [Fintype V] {G : SimpleGraph V} (hG : G.Connected) [G.LocallyFinite] :
   ∃ (a b : V), ∃ (p : G.Walk a b), Walk.IsMaxlongPath p := by
  obtain H' := exists_maximal_path hG
  let S : (a b : V) → Set (G.Walk a b) := fun a b => {p | p.IsPath}
  let lengths  := {n | ∃ (c d : V), ∃ (q : G.Walk c d), q.IsPath ∧ q.length = n }
  have lengths_Finite : lengths.Finite := by
    let N := Fintype.card V
    have bound : ∀ n ∈ lengths, n ≤ Fintype.card V := by
      intro n hn
      rcases hn with ⟨c,d, p, hp, rfl⟩
      have h_card : p.support.length ≤ Fintype.card V := by
        exact List.Nodup.length_le_card hp.support_nodup
      simp_all only [SimpleGraph.Walk.length_support, ge_iff_le]
      omega
    have finite_bounded : Set.Finite {n : ℕ | n ≤ Fintype.card V} := by
      obtain H := Set.finite_le_nat (n := Fintype.card V)
      simp_all only
    exact Set.Finite.subset finite_bounded bound
  have lengths_Nonempty : lengths.Nonempty := by
    rw [Set.nonempty_def]
    have : ∃ (c d : V), ∃ (q : G.Walk c d), Walk.IsMaximalPath q := by
      simp_all only [exists_const_iff, and_true, and_self]
      rcases hG with ⟨h⟩
      omega
    rcases this with ⟨c,d, q, hq⟩
    refine ⟨q.length,c, d, q, hq.1, rfl⟩
  obtain maximal := Set.Finite.exists_maximal (h := lengths_Finite) (hs := lengths_Nonempty)
  rcases maximal with ⟨i, hi⟩
  unfold Walk.IsMaxlongPath
  rw [maximal_mem_iff] at hi
  have : ∃ (c d : V),  ∃ (q : G.Walk c d), q.IsPath ∧ q ∈ S c d := by
    rcases hi with ⟨hi_mem, hi_max⟩
    unfold lengths at hi_mem
    simp_rw [Set.mem_setOf_eq] at hi_mem
    rcases hi_mem with ⟨c,d,q, hp_is_path, hp_length⟩
    refine ⟨c,d,q, hp_is_path, ?_⟩
    simp only [Set.mem_setOf_eq, hp_is_path, S]
  rcases this with ⟨c, d, q, hp, h⟩
  have :∃ (a b : V), ∃ (p : G.Walk a b), p.length = i ∧ p ∈ S a b := by
    rcases hi with ⟨hi_mem, hi_max⟩
    unfold lengths at hi_mem
    simp_rw [Set.mem_setOf_eq] at hi_mem
    rcases hi_mem with ⟨a, b, p, hp_is_path, hp_length⟩
    refine ⟨a, b, p, hp_length, ?_⟩
    simp only [Set.mem_setOf_eq, S]
    simp_all only
  rcases this with ⟨a,b,p, hp,h⟩
  simp only [S, Set.mem_setOf_eq] at h
  use a
  use b
  use p
  constructor
  · exact h
  · intro c d q hq
    have : q.length ∈ lengths := by
      unfold lengths
      simp only [Set.mem_setOf_eq]
      use c
      use d
      use q
    simp_all only [ge_iff_le]
    rcases hi with ⟨hi_mem, hi_max⟩
    obtain := hi_max (y := q.length) this
    omega


/--
The length of a path `p` truncated to a certain vertex equals the length of the vertex list.
-/
lemma length_takeUntil_eq_index [DecidableEq V] {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (u : V) (h : u ∈ p.support) (g : List.idxOf u p.support ≤ p.length) (hp_path : p.IsPath) :
  (p.takeUntil _ h).length = p.support.idxOf u := by
  have l : (p.takeUntil u h).length < p.support.length := by
    calc
    _ ≤ p.length := by
      apply SimpleGraph.Walk.length_takeUntil_le
    _ < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      linarith
  have idx_x : p.support.idxOf (p.support.get ⟨(p.takeUntil _ h).length, l⟩) =
    (p.takeUntil _ h).length := by
    apply List.Nodup.idxOf_getElem
    exact hp_path.support_nodup
  have l1 : p.getVert (p.support.idxOf u) = u := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
    · simp
    · exact g
  rw [SimpleGraph.Walk.getVert_eq_support_getElem] at l1
  · obtain h := SimpleGraph.Walk.getVert_length_takeUntil h
    rw [SimpleGraph.Walk.getVert_eq_support_getElem] at h
    conv at h =>
      right;
      rw [← l1]
    · rw [List.Nodup.getElem_inj_iff] at h
      · exact h
      · exact hp_path.support_nodup
    · apply SimpleGraph.Walk.length_takeUntil_le
  · exact g


/--
For a path `G.Walk a b` in graph `G`, if there exists a vertex `v` not on this path,
then the two endpoints `a` and `b` of the path are not adjacent.
-/
lemma ore_endpoints_adjacent [Fintype V] {G : SimpleGraph V} (hG : G.Connected) [G.LocallyFinite] {a b : V} {p : G.Walk a b} (hp : Walk.IsMaxlongPath p) (hv_not_in_p : ∃ (v : V), v ∉ p.support) :
  ¬ G.Adj a b := by
  rcases hv_not_in_p with ⟨v, hv_not_in_p⟩
  intro H_adj
  classical
  have H  :∃ (j : ℕ), G.Reachable v (p.getVert (j))  ∧
      ∃  (s : G.Walk v (p.getVert (j))), s.IsPath ∧ s.support ∩ p.support = {p.getVert (j)} := by
    let S : (a  : V) → Set (G.Walk v a) := fun a =>  {s | s.IsPath ∧ a ∈ p.support}
    let lengths  := {n | ∃ (a : V), ∃ (s : G.Walk v a), s.IsPath ∧ a ∈ p.support ∧ s.length = n }
    have l1 : lengths.Finite := by
      let N := Fintype.card V
      have bound : ∀ n ∈ lengths, n ≤ Fintype.card V := by
        intro n hn
        rcases hn with ⟨c,p, hp, hq, rfl⟩
        have h_nodup : p.support.Nodup := hp.support_nodup
        have h_card : p.support.length ≤ Fintype.card V := by
          exact List.Nodup.length_le_card h_nodup
        have length_eq : p.length = p.support.length - 1 := by
          simp only [SimpleGraph.Walk.length_support, add_tsub_cancel_right]
        rw [length_eq]
        omega
      have finite_bounded : Set.Finite {n : ℕ | n ≤ Fintype.card V} := by
        obtain H := Set.finite_le_nat (n := Fintype.card V)
        simp_all
      exact Set.Finite.subset finite_bounded bound
    have h_lengths_nonempty : lengths.Nonempty := by
      rw [Set.nonempty_def]
      have h_reachable : ∃ w ∈ p.support, G.Reachable v w := by
        use a
        have ha_pos : a ∈ p.support := by
          obtain l := SimpleGraph.Walk.start_mem_support p
          omega
        refine ⟨ha_pos, ?_⟩
        exact hG v a
      rcases h_reachable with ⟨w, hw, h_reach⟩
      have : ∃ (q : G.Walk v w), q.IsPath := by
        obtain h := SimpleGraph.Reachable.exists_isPath h_reach
        omega
      rcases this with ⟨q, hq⟩
      use q.length
      refine ⟨w, q, hq, hw, rfl⟩
    obtain h_min_length := Set.Finite.exists_minimal (h := l1) (hs := h_lengths_nonempty)
    rcases h_min_length with ⟨min_len, h_min, hs_length⟩
    have :∃  (a : V), ∃ (p : G.Walk v a), p.length = min_len ∧ p ∈ S a := by
      unfold lengths at h_min
      simp_rw [Set.mem_setOf_eq] at h_min
      rcases h_min with ⟨a,p, hp_is_path, hp_length⟩
      refine ⟨a,p,  ?_⟩
      unfold S
      simp_all
    rcases this with ⟨a,s, hp,h⟩
    unfold S at h
    simp only [Set.mem_setOf_eq] at h
    let k := p.support.idxOf a
    have hw : p.getVert k = a := by
      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
      · simp only [getElem_idxOf, k]
      · have : k < p.support.length := by
          apply List.idxOf_lt_length_iff.mpr
          exact h.2
        simp_all only [SimpleGraph.Walk.length_support]
        linarith
    use k
    rw [hw]
    obtain l := SimpleGraph.Walk.reachable s
    refine ⟨ l , s, h.1, ?_⟩
    by_cases h_has_other : ∃ x ∈ s.support ∩ p.support, x ≠ a
    · rcases h_has_other with ⟨x, h , hx_ne⟩
      have hx_pos : x ∈ s.support := by
          exact List.mem_of_mem_inter_left h
      have hx_in_p : x ∈ p.support := by
        exact List.mem_of_mem_inter_right h
      have hw_in_p : a ∈ p.support := by simp_all
      let s' := s.takeUntil x hx_pos
      have l : s.IsPath  := by simp_all
      have hs'_path : s'.IsPath := by
        simp only [s']
        exact l.takeUntil hx_pos
      have hs'_len : s'.length < s.length := by
        obtain h := SimpleGraph.Walk.length_takeUntil_lt hx_pos hx_ne
        simp only [s']
        exact h
      have hs'_cand : s' ∈ S x  := by
        simp only [Set.mem_setOf_eq, S]
        refine ⟨hs'_path, hx_in_p⟩
      have hs'_cand : s'.length ∈ lengths  := by
        simp only [Set.mem_setOf_eq, lengths]
        refine ⟨x, s', hs'_path, hx_in_p, rfl⟩
      have : s'.length < min_len := by
        rw [hp] at hs'_len
        exact hs'_len
      obtain l' := le_of_lt this
      obtain l := hs_length  hs'_cand l'
      linarith
    · have l1 : a ∈ p.support := by
        exact h.2
      have l2 : a ∈ s.support := by
        obtain := SimpleGraph.Walk.end_mem_support s
        omega
      obtain  h :=  List.mem_inter_of_mem_of_mem l1 l2
      simp only [mem_inter_iff, ne_eq, not_exists, not_and, Decidable.not_not,
        and_imp] at h_has_other
      have h_support_eq (hs_inter : s.support.toFinset ∩ p.support.toFinset = {a}):
          s.support ∩ p.support = {a} := by
        rw [← List.toFinset_inter] at hs_inter
        have : ({a} :Finset V) =  ({a} : List V).toFinset := by
          ext x
          rw [Finset.mem_singleton, List.mem_toFinset]
          constructor
          · intro h
            rw [← List.mem_singleton] at h
            omega
          · intro h
            rw [← List.mem_singleton]
            omega
        have l': (s.support ∩ p.support).Nodup := by
          apply List.Nodup.inter
          rename_i h
          rename_i h1
          exact h1.1.support_nodup
        rw [this, ← List.toFinset_eq (n := l')] at hs_inter
        have : (({a} : List V)).Nodup := by
          rw [List.singleton_eq]
          apply List.nodup_singleton
        conv at hs_inter =>
          rw [← List.toFinset_eq this]
          simp
        rw [List.perm_comm, List.singleton_eq,
          List.singleton_perm (a := a) (l := s.support ∩ p.support)] at hs_inter
        rw [List.singleton_eq, hs_inter]
      rw [h_support_eq]
      apply Finset.Subset.antisymm
      · simp_all only [SimpleGraph.Walk.start_mem_support, and_true,
        SimpleGraph.Walk.end_mem_support, List.mem_inter_iff, and_self,Finset.subset_singleton_iff]
        right
        ext x
        constructor
        · intro h
          simp_all only [SimpleGraph.Walk.start_mem_support, SimpleGraph.Walk.end_mem_support,
            Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
        · intro h
          simp_all only [SimpleGraph.Walk.start_mem_support, SimpleGraph.Walk.end_mem_support,
            Finset.mem_singleton, Finset.mem_inter, List.mem_toFinset, and_self]
      · simp_all only [SimpleGraph.Walk.start_mem_support, and_true,
        SimpleGraph.Walk.end_mem_support, List.mem_inter_iff, and_self, Finset.singleton_subset_iff,
        Finset.mem_inter, List.mem_toFinset]
  rcases H with ⟨j, h_reach, s, hs_path, hs_inter⟩
  rcases Decidable.em (j < p.length) with hJ | hJ
  · have h1 : p.getVert j ∈  p.support := by
      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
      · simp only [List.getElem_mem]
      · have : j < p.length := by
          omega
        omega
    have h2 : p.getVert (j + 1) ∈  p.support := by
      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
      · simp only [List.getElem_mem]
      · have : j + 1 ≤ p.length := by
          omega
        omega
    let eady_ja : G.Walk (p.getVert j) a  := (p.takeUntil (p.getVert j) h1).reverse
    let eady_va : G.Walk v a := s.append eady_ja
    have h2' : p.getVert (j + 1) ∈ p.reverse.support := by
      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
      · simp only [support_reverse, mem_reverse, getElem_mem]
      · have : j + 1 ≤ p.length := by
          omega
        omega
    let eady_bj_succ : G.Walk b (p.getVert (j + 1)) := (p.reverse.takeUntil (p.getVert (j + 1)) h2')
    let q :  G.Walk (p.getVert (j + 1)) v :=  eady_bj_succ.reverse.append (Walk.cons H_adj.symm eady_va.reverse)
    unfold Walk.IsMaxlongPath at hp
    obtain ⟨hp_path, hp_max⟩ := hp
    obtain h := hp_max (p.getVert (j + 1)) v q
    have hq_path : q.IsPath := by
      unfold q
      rw [SimpleGraph.Walk.isPath_def]
      obtain H := List.nodup_append'  (l₁ :=  (p.reverse.takeUntil (p.getVert (j + 1)) h2').support.reverse) (l₂ := ((p.takeUntil (p.getVert j) h1).append s.reverse).support)
      have : (eady_bj_succ.reverse.append (Walk.cons H_adj.symm eady_va.reverse)).support =
        (eady_bj_succ.reverse.support ++ (Walk.cons H_adj.symm eady_va.reverse).support.tail) := by
        rw [Walk.support_append]
      rw [this]
      simp only [support_reverse, Walk.reverse_append, Walk.reverse_reverse, support_cons,
        List.tail_cons, eady_bj_succ, eady_va, eady_ja]
      rw [H]
      constructor
      · simp only [nodup_reverse]
        rw [← SimpleGraph.Walk.isPath_def]
        apply SimpleGraph.Walk.IsPath.takeUntil
        simp only [isPath_reverse_iff]
        exact hp_path
      · constructor
        · obtain H := List.nodup_append'  (l₁ :=(p.takeUntil (p.getVert j) h1).support) (l₂ := s.reverse.support.tail)
          have : ((p.takeUntil (p.getVert j) h1).append s.reverse).support =
            ((p.takeUntil (p.getVert j) h1).support ++ s.reverse.support.tail) := by
            rw [Walk.support_append]
          rw [this, H]
          constructor
          · rw [← SimpleGraph.Walk.isPath_def]
            apply SimpleGraph.Walk.IsPath.takeUntil
            exact hp_path
          · constructor
            · rw [← SimpleGraph.Walk.support_tail_of_not_nil]
              · rw [← SimpleGraph.Walk.isPath_def]
                apply SimpleGraph.Walk.IsPath.tail
                apply SimpleGraph.Walk.IsPath.reverse
                exact hs_path
              · intro H
                rw [SimpleGraph.Walk.nil_reverse] at H
                obtain H' := SimpleGraph.Walk.Nil.eq H
                have : p.getVert j ∈ p.support := by omega
                rw [← H'] at this
                contradiction
            · have H3 : (p.takeUntil (p.getVert j) h1).support.Disjoint s.reverse.support.tail := by
                rw [← List.inter_eq_nil_iff_disjoint]
                rw [← List.toFinset_eq_empty_iff]
                simp only [support_reverse, tail_reverse, inter_reverse, toFinset_inter]
                apply Finset.Subset.antisymm
                · intro x hx
                  rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                  have h1 : p.getVert j ∈ p.support := by omega
                  simp only [mem_toFinset] at hx_left
                  simp only [mem_toFinset] at hx_right
                  have h_indices_left : x ∈ p.support := by
                    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                    rcases hx_left with ⟨k , hk, hj⟩
                    rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                    · rw [← hk]
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                      · simp only [getElem_mem]
                      · have len : (p.takeUntil (p.getVert j) h1).length ≤ p.length := by
                          apply SimpleGraph.Walk.length_takeUntil_le
                        omega
                    · exact hj
                  have h_indices_right : ¬ x ∈ p.support := by
                    by_contra H
                    obtain h := List.mem_of_mem_dropLast hx_right
                    obtain h' := List.mem_inter_of_mem_of_mem h h_indices_left
                    rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                    have h'' : s.support ≠ [] := by
                      simp_all
                    have s_eq : (s.support.dropLast ++ [p.getVert j]).reverse= s.support.reverse := by
                      rw [← List.dropLast_append_getLast (l := s.support)]
                      · simp only [getLast_support, ne_eq, cons_ne_self, not_false_eq_true,
                        dropLast_append_of_ne_nil, dropLast_singleton, List.append_nil]
                      · exact h''
                    rw [List.reverse_concat'] at s_eq
                    have l : (s.support.reverse).Nodup := by
                      simp only [nodup_reverse]
                      exact hs_path.support_nodup
                    rw [← s_eq] at l
                    obtain  H:= List.Nodup.notMem  l
                    have : x ∉ s.support.dropLast.reverse := by
                      rw [h']
                      exact H
                    simp only [mem_reverse] at this
                    contradiction
                  contradiction
                · apply Finset.empty_subset
              exact H3
        · have H4 : (p.reverse.takeUntil (p.getVert (j + 1)) h2').support.reverse.Disjoint
            ((p.takeUntil (p.getVert j) h1).append s.reverse).support := by
            rw [← List.inter_eq_nil_iff_disjoint]
            rw [← List.toFinset_eq_empty_iff]
            simp only [toFinset_inter, toFinset_reverse]
            apply Finset.Subset.antisymm
            · intro x hx
              rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
              have h1 : p.getVert j ∈ p.support := by omega
              simp only [mem_toFinset] at hx_left
              simp only [mem_toFinset, mem_support_append_iff, support_reverse,
                mem_reverse] at hx_right
              have h_indices_left : ∃ k, p.reverse.getVert k = x ∧ k ≤ p.length - (j + 1) := by
                rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                rcases hx_left with ⟨k , hk, hj⟩
                rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                · use k
                  simp_all only [getVert_mem_support, implies_true, nodup_reverse,
                    disjoint_reverse_left, support_reverse, support_cons, List.tail_cons, mem_inter,
                    mem_toFinset, mem_support_append_iff, mem_reverse, and_true, true_and]
                  have h1 : p.getVert (j + 1) ∈ p.reverse.support := by
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                    · simp only [support_reverse, mem_reverse, getElem_mem]
                    · have : j + 1 ≤ p.length := by
                        omega
                      omega
                  have : p.reverse.getVert (p.reverse.takeUntil (p.getVert (j + 1)) h2').length =  p.reverse.getVert (p.length - (j + 1)) := by
                    rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
                    rw [Nat.sub_sub_self]
                    have l': j  < p.length := by
                      omega
                    linarith
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                  · have l : (p.length - (j + 1)) ≤ p.reverse.length := by
                      simp
                    conv at this =>
                      right;
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l]
                      rfl
                    rw [List.Nodup.getElem_inj_iff] at this
                    · rw [this] at hj
                      exact hj
                    · simp only [support_reverse, nodup_reverse]
                      exact hp_path.support_nodup
                  · apply SimpleGraph.Walk.length_takeUntil_le
                · exact hj
              rcases hx_right with (hx_right'| hx_right')
              · have h_indices_right : ∃ k, p.getVert k = x ∧ k ≤ j := by
                  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_right'
                  rcases hx_right'  with ⟨k , hk, hj⟩
                  rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                  · use k
                    simp_all only [getVert_mem_support, implies_true, nodup_reverse,
                      disjoint_reverse_left, support_reverse, support_cons, List.tail_cons,
                      mem_inter, mem_toFinset, mem_support_append_iff, mem_reverse, true_and]
                    have h1 : p.getVert j ∈ p.support := by
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                      · simp only [getElem_mem]
                      · have : j  ≤ p.length := by
                          omega
                        omega
                    have : p.getVert (p.takeUntil (p.getVert j) h1).length =  p.getVert j := by
                      rw [SimpleGraph.Walk.getVert_length_takeUntil]
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                    · have l : j ≤ p.length := by
                        omega
                      conv at this =>
                        right;
                        rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                        rfl
                      rw [List.Nodup.getElem_inj_iff] at this
                      · rw [this] at hj
                        exact hj
                      · exact hp_path.support_nodup
                    · apply SimpleGraph.Walk.length_takeUntil_le
                  · exact hj
                rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                rw [SimpleGraph.Walk.getVert_reverse] at hk₁_eq
                rw [← hk₂_eq] at hk₁_eq
                have hk_eq : k₁ =  p.length - k₂ := by
                  simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
                    getVert_eq_support_getElem] at hk₁_eq
                  have l': k₂ ≤  p.length := by
                    omega
                  have l : j ≤ p.length := by linarith
                  have l :(p.length - k₁) ≤ p.length := by omega
                  rename_i hk₂_eq'
                  conv at hk₁_eq =>
                    right
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem p l']
                  rw [List.Nodup.getElem_inj_iff] at hk₁_eq
                  · omega
                  · exact hp_path.support_nodup
                rw [hk_eq] at hk₁_ge
                omega
              · have h_indices_left'' : x ∈ p.support := by
                  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                  rcases hx_left with ⟨k , hk, hj⟩
                  rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                  · rw [← hk]
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                    · simp only [support_reverse, getElem_reverse, length_support,
                      add_tsub_cancel_right, getElem_mem]
                    · have l : p.getVert j ∈ p.reverse.support := by
                        simp
                      have len : (p.reverse.takeUntil (p.getVert (j + 1)) h2').length ≤ p.reverse.length := by
                        apply SimpleGraph.Walk.length_takeUntil_le
                      omega
                  · exact hj
                rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                obtain h' := List.mem_inter_of_mem_of_mem hx_right' h_indices_left''
                rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                rw [h', SimpleGraph.Walk.getVert_reverse] at hk₁_eq
                have l1 : (p.length - k₁) ≤ p.length := by omega
                have l2 : j ≤ p.length := by linarith
                rw [SimpleGraph.Walk.getVert_eq_support_getElem p l1] at hk₁_eq
                conv at hk₁_eq =>
                  right
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem p l2]
                rw [List.Nodup.getElem_inj_iff] at hk₁_eq
                · omega
                · exact hp_path.support_nodup
            · apply Finset.empty_subset
          exact H4
    have hq_length : q.length = s.length + p.length := by
      unfold q
      simp only [Walk.reverse_append, Walk.reverse_reverse, Walk.length_append, Walk.length_reverse,
        Walk.length_cons, eady_bj_succ, eady_va, eady_ja]
      obtain H := SimpleGraph.Walk.getVert_length_takeUntil h1
      have l1 : (p.takeUntil (p.getVert j) h1).length ≤ p.length := by
        apply SimpleGraph.Walk.length_takeUntil_le
      have l2 : j ≤ p.length := by
        omega
      rw [SimpleGraph.Walk.getVert_eq_support_getElem p l1] at H
      conv at H =>
        right;
        rw [SimpleGraph.Walk.getVert_eq_support_getElem p l2]
      rw [List.Nodup.getElem_inj_iff] at H
      · rw [H]
        have h2' : p.getVert (j + 1) ∈ p.reverse.support := by
          rw [SimpleGraph.Walk.getVert_eq_support_getElem]
          · simp only [support_reverse, mem_reverse, getElem_mem]
          · have : j + 1 ≤ p.length := by
              omega
            omega
        obtain H := SimpleGraph.Walk.getVert_length_takeUntil h2'
        have l3 : (p.reverse.takeUntil (p.getVert (j + 1)) h2').length ≤ p.reverse.length := by
          apply SimpleGraph.Walk.length_takeUntil_le
        have l4 : j + 1 ≤ p.length := by omega
        rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l3] at H
        have l5 : p.length - (j + 1) ≤ p.reverse.length := by
          simp
        have : p.getVert (j + 1) = p.reverse.getVert (p.length - (j + 1)) := by
          rw [SimpleGraph.Walk.getVert_reverse, Nat.sub_sub_self l4]
        conv at H =>
          right;
          rw [this]
          rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l5]
        rw [List.Nodup.getElem_inj_iff] at H
        · rw [H, add_right_comm, ← Nat.add_assoc, Nat.sub_add_cancel]
          · linarith
          · omega
        · simp only [support_reverse, nodup_reverse]
          exact hp_path.support_nodup
      · exact hp_path.support_nodup
    have len_le : q.length > p.length := by
      rw [hq_length]
      simp only [gt_iff_lt, lt_add_iff_pos_left]
      rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
      intro H
      obtain H' := SimpleGraph.Walk.Nil.eq H
      simp_all
    have := h hq_path
    linarith [hq_length , this]
  · have hJ : p.length ≤ j := by linarith
    obtain eq := SimpleGraph.Walk.getVert_of_length_le p hJ
    let s' : G.Walk v b := s.copy rfl eq
    have s'_path : s'.IsPath := by
      unfold s'
      simp only [isPath_copy]
      exact hs_path
    let q  : G.Walk a v := p.append s'.reverse
    have hq_path : q.IsPath := by
      unfold q
      rw [SimpleGraph.Walk.isPath_def]
      obtain H := List.nodup_append' (l₁ := p.support) (l₂ := s'.reverse.support.tail)
      have :  (p.append s'.reverse).support = (p.support ++ (s'.reverse).support.tail) := by
        rw [Walk.support_append]
      rw [this, H]
      constructor
      · unfold Walk.IsMaxlongPath at hp
        exact hp.1.support_nodup
      · constructor
        · rw [← SimpleGraph.Walk.support_tail_of_not_nil]
          · rw [← SimpleGraph.Walk.isPath_def]
            apply SimpleGraph.Walk.IsPath.tail
            apply SimpleGraph.Walk.IsPath.reverse
            exact s'_path
          · intro H
            rw [SimpleGraph.Walk.nil_reverse] at H
            obtain H' := SimpleGraph.Walk.Nil.eq H
            simp_all
        · have H3 : p.support.Disjoint s'.reverse.support.tail := by
            rw [← List.inter_eq_nil_iff_disjoint]
            rw [← List.toFinset_eq_empty_iff]
            simp only [support_reverse, tail_reverse, inter_reverse, toFinset_inter]
            apply Finset.Subset.antisymm
            · intro x hx
              rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
              have h1 : x ∈ p.support := by
                simpa using hx_left
              simp only [mem_toFinset] at hx_right
              have h_indices_left : x ∈ p.support := by omega
              have h_indices_right : ¬ x ∈ p.support := by
                by_contra H
                obtain h := List.mem_of_mem_dropLast hx_right
                obtain h' := List.mem_inter_of_mem_of_mem h h_indices_left
                obtain h_copy := SimpleGraph.Walk.support_copy s rfl eq
                rw [← h_copy] at hs_inter
                rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                have h'' : s'.support ≠ [] := by
                  simp_all only [not_lt, support_reverse, tail_reverse, nodup_reverse,
                    disjoint_reverse_right, mem_inter, mem_toFinset, end_mem_support, true_and,
                    support_copy, ne_eq, support_ne_nil, not_false_eq_true]
                have s_eq : (s'.support.dropLast ++ [p.getVert (j)]).reverse =
                  s'.support.reverse := by
                  rw [← List.dropLast_append_getLast (l := s'.support)]
                  · simp only [getLast_support, ne_eq, cons_ne_self, not_false_eq_true,
                      dropLast_append_of_ne_nil, dropLast_singleton, List.append_nil]
                    rw [eq]
                  · exact h''
                rw [List.reverse_concat'] at s_eq
                have l : (s'.support.reverse).Nodup := by
                  simp only [nodup_reverse]
                  exact s'_path.support_nodup
                rw [← s_eq] at l
                obtain  H := List.Nodup.notMem  l
                have : x ∉ s'.support.dropLast.reverse := by
                  rw [h']
                  exact H
                simp only [mem_reverse] at this
                contradiction
              contradiction
            · apply Finset.empty_subset
          exact H3
    have hq_length : q.length = p.length + s'.length := by
      simp only [Walk.length_append, Walk.length_reverse, q]
    have len_le : q.length > p.length := by
      rw [hq_length]
      have : 0 < s'.length:= by
        rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
        intro H
        obtain H' := SimpleGraph.Walk.Nil.eq H
        simp_all
      omega
    unfold Walk.IsMaxlongPath at hp
    have := hp.2 a v q hq_path
    linarith [hq_length , this]


/--
The longest path `G.Walk a b` in a graph, if there exists a vertex `v` not on this path,
then the two endpoints `a` and `b` of the path are not equal.
-/
lemma endpoint_ne [Fintype V] {G : SimpleGraph V} [G.LocallyFinite] {hG : G.Connected} {a b : V} (p : G.Walk a b) (hp : Walk.IsMaxlongPath p) {h_order : Fintype.card V ≥ 3} (hv_not_in_p : ∃ (v : V), v ∉ p.support) :
  a ≠ b := by
  unfold Walk.IsMaxlongPath at hp
  obtain ⟨hp_path, hp_max⟩ := hp
  rcases hv_not_in_p with ⟨v, hv_not_in_p⟩
  by_contra! h_eq
  simp_all only [ge_iff_le]
  by_cases H' : p.Nil
  · have : p.length = 0 := by
      rw [SimpleGraph.Walk.nil_iff_length_eq] at H'
      omega
    obtain h := SimpleGraph.connected_iff_exists_forall_reachable G
    rw [h] at hG
    rcases hG with ⟨q,hq⟩
    obtain hv := hq v
    simp_all only [nonpos_iff_eq_zero]
    obtain ⟨w, hw_ne⟩ : ∃ w : V, w ≠ q := by
      have : 1 < Fintype.card V := by linarith
      obtain h := Fintype.exists_ne_of_one_lt_card this q
      omega
    have h_reach : G.Reachable q w := hq w
    obtain ⟨r, hr_path⟩ : ∃ (r : G.Walk q w), r.IsPath := by
      obtain h := SimpleGraph.Reachable.exists_isPath h_reach
      omega
    have h_length : r.length = 0 := hp_max q w r hr_path
    have h_eq_qw : q = w := by
      rw [← SimpleGraph.Walk.nil_iff_length_eq] at h_length
      obtain h := SimpleGraph.Walk.Nil.eq h_length
      omega
    exact hw_ne h_eq_qw.symm
  · subst h_eq
    obtain h := SimpleGraph.Walk.isPath_iff_eq_nil p
    rw [h] at hp_path
    simp_all only [Walk.length_nil, nonpos_iff_eq_zero, support_nil, List.mem_cons, not_mem_nil,
      or_false, nil_nil, not_true_eq_false]

/--
The length of path p take to a certain vertex with "takeUntil".
-/
lemma len_takeUntil {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]
    {a b : V} (p : G.Walk a b) {i : ℕ} {hp : p.IsPath} {hn : i ≤ p.length} {hi : p.getVert i ∈ p.support} :
  (p.takeUntil _ hi).length = i := by
  rw [length_takeUntil_eq_index]
  · rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
    · exact hp.support_nodup
    · linarith
  · rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
    · linarith
    · exact hp.support_nodup
    · linarith
  · exact hp

/--
The length of the reverse of path p take to a certain vertex with "takeUntil".
-/
lemma len_reverse_takeUntil {G : SimpleGraph V} [DecidableEq V] {a b : V} (p : G.Walk a b) {hp : p.IsPath} {i : ℕ} {hi : p.getVert i ∈ p.reverse.support} :
  (p.reverse.takeUntil _ hi).length = p.length - i := by
  obtain H := SimpleGraph.Walk.getVert_length_takeUntil hi
  rw [SimpleGraph.Walk.getVert_eq_support_getElem] at H
  · have : p.getVert i = p.reverse.getVert (p.reverse.length - i) := by
      rw [← SimpleGraph.Walk.getVert_reverse (p := p.reverse)]; simp
    have l : p.reverse.length - i ≤ p.reverse.length := by omega
    conv at H =>
      right; rw [this, SimpleGraph.Walk.getVert_eq_support_getElem (h := l)]; rfl
    rw [List.Nodup.getElem_inj_iff, SimpleGraph.Walk.length_reverse] at H
    · rw [H]
    rw [← SimpleGraph.Walk.isPath_def]
    simp only [isPath_reverse_iff]
    exact hp
  · apply SimpleGraph.Walk.length_takeUntil_le

/--
If there exists a vertex v outside the longest simple path p that is not on path p,
then there exists a simple path s starting from v with its endpoint being the first
point where it connects to path p , and p and s intersect only at the point.
-/
lemma exsist_walk {G : SimpleGraph V} [Fintype V] [DecidableEq V] [G.LocallyFinite]
    {hG : G.Connected} {a b : V} (p : G.Walk a b) {i : Fin (p.support.length - 1)} (hp : Walk.IsMaxlongPath p) :
    ∀ (v : V), ∃ (j : ℕ), G.Reachable v (p.getVert j) ∧ ∃ (s : G.Walk v (p.getVert j)), s.IsPath ∧ s.support ∩ p.support = {p.getVert j} := by
  intro v
  unfold Walk.IsMaxlongPath at hp
  obtain ⟨hp_path, hp_max⟩ := hp
  let S : (a  : V) → Set (G.Walk v a) := fun a =>  {s | s.IsPath ∧ a ∈ p.support}
  let lengths  := {n | ∃ (a : V), ∃ (s : G.Walk v a), s.IsPath ∧ a ∈ p.support ∧ s.length = n }
  have l1 : lengths.Finite := by
    let N := Fintype.card V
    have bound : ∀ n ∈ lengths, n ≤ Fintype.card V := by
      intro n hn
      rcases hn with ⟨c,p, hp, hq, rfl⟩
      have h_nodup : p.support.Nodup := hp.support_nodup
      have h_card : p.support.length ≤ Fintype.card V := by
        exact List.Nodup.length_le_card h_nodup
      have length_eq : p.length = p.support.length - 1 := by
        simp only [length_support, add_tsub_cancel_right]
      rw [length_eq]
      omega
    have finite_bounded : Set.Finite {n : ℕ | n ≤ Fintype.card V} := by
      obtain H := Set.finite_le_nat (n := Fintype.card V)
      simp_all only
    exact Set.Finite.subset finite_bounded bound
  have h_lengths_nonempty : lengths.Nonempty := by
    rw [Set.nonempty_def]
    have h_reachable : ∃ w ∈ p.support, G.Reachable v w := by
      use p.support[i.val + 1]
      constructor
      · simp
      · exact hG v p.support[i.val + 1]
    rcases h_reachable with ⟨w, hw, h_reach⟩
    have : ∃ (q : G.Walk v w), q.IsPath := by
      obtain h := SimpleGraph.Reachable.exists_isPath h_reach
      omega
    rcases this with ⟨q, hq⟩
    use q.length
    refine ⟨w, q, hq, hw, rfl⟩
  obtain h_min_length := Set.Finite.exists_minimal (h := l1) (hs := h_lengths_nonempty)
  rcases h_min_length with ⟨min_len, h_min, hs_length⟩
  have :∃ (a : V), ∃ (p : G.Walk v a), p.length = min_len ∧ p ∈ S a := by
    unfold lengths at h_min
    simp_rw [Set.mem_setOf_eq] at h_min
    rcases h_min with ⟨a, p, hp_is_path, hp_length⟩
    refine ⟨a, p, ?_⟩
    unfold S
    simp_all only [and_true, Set.mem_setOf_eq, and_self]
  rcases this with ⟨a, s, hp, h⟩
  unfold S at h
  simp only [Set.mem_setOf_eq] at h
  let k := p.support.idxOf a
  have hw : p.getVert k = a := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
    · simp only [getElem_idxOf, k]
    · have : k < p.support.length := by
        apply List.idxOf_lt_length_iff.mpr
        exact h.2
      simp_all only [ge_iff_le, length_support]
      linarith
  use k
  rw [hw]
  obtain l := SimpleGraph.Walk.reachable s
  refine ⟨l, s, h.1, ?_⟩
  by_cases h_has_other : ∃ x ∈ s.support ∩ p.support, x ≠ a
  · rcases h_has_other with ⟨x, h , hx_ne⟩
    have hx_pos : x ∈ s.support := by
        obtain l := List.mem_of_mem_inter_left h
        exact l
    have hx_in_p : x ∈ p.support := by
      obtain l := List.mem_of_mem_inter_right h
      exact l
    have hw_in_p : a ∈ p.support := by simp_all only [ne_eq, mem_inter_iff,
      and_self]
    let s' := s.takeUntil x hx_pos
    have l : s.IsPath  := by simp_all only [ne_eq, and_true, mem_inter_iff,
      and_self]
    have hs'_path : s'.IsPath := by
      simp only [s']
      obtain this := l.takeUntil hx_pos
      exact this
    have hs'_len : s'.length < s.length := by
      obtain h := SimpleGraph.Walk.length_takeUntil_lt hx_pos hx_ne
      simp only [s']
      exact h
    have hs'_cand : s' ∈ S x  := by
      simp only [Set.mem_setOf_eq, S]
      refine ⟨hs'_path, hx_in_p⟩
    have hs'_cand : s'.length ∈ lengths  := by
      simp only [Set.mem_setOf_eq, lengths]
      refine ⟨x, s', hs'_path, hx_in_p, rfl⟩
    have : s'.length < min_len := by
      rw [hp] at hs'_len
      exact hs'_len
    obtain l' := le_of_lt this
    obtain l := hs_length hs'_cand l'
    linarith
  · have l1 : a ∈ p.support := by
      exact h.2
    have l2 : a ∈ s.support := by
      obtain := SimpleGraph.Walk.end_mem_support s
      omega
    obtain  h :=  List.mem_inter_of_mem_of_mem l1 l2
    simp only [mem_inter_iff, ne_eq, not_exists, not_and, Decidable.not_not, and_imp] at h_has_other
    have h_support_eq (hs_inter : s.support.toFinset ∩ p.support.toFinset = {a}):
        s.support ∩ p.support = {a} := by
      rw [← List.toFinset_inter] at hs_inter
      have : ({a} :Finset V) =  ({a} : List V).toFinset := by
        ext x
        simp only [Finset.mem_singleton, mem_toFinset]
        constructor
        · intro h
          rw [← List.mem_singleton] at h
          omega
        · intro h
          rw [← List.mem_singleton]
          omega
      have l': (s.support ∩ p.support).Nodup := by
        apply List.Nodup.inter
        rename_i h
        rename_i h1
        exact h1.1.support_nodup
      rw [this, ← List.toFinset_eq (n := l')] at hs_inter
      have : (({a} : List V)).Nodup := by
        rw [List.singleton_eq]
        apply List.nodup_singleton
      conv at hs_inter =>
        rw [← List.toFinset_eq this]
        simp
      rw [List.perm_comm, List.singleton_eq,
        List.singleton_perm (a := a) (l := s.support ∩ p.support)] at hs_inter
      rw [List.singleton_eq, hs_inter]
    rw [h_support_eq]
    apply Finset.Subset.antisymm
    · simp_all only [start_mem_support, and_true, end_mem_support,
      mem_inter_iff, and_self, Finset.subset_singleton_iff]
      right; ext x
      constructor
      · intro h
        simp_all only [start_mem_support, end_mem_support, mem_inter, mem_toFinset,
          Finset.mem_singleton]
      · intro h
        simp_all only [start_mem_support, end_mem_support, Finset.mem_singleton, mem_inter,
          mem_toFinset, and_self]
    · simp_all only [start_mem_support, and_true, end_mem_support,
      mem_inter_iff, and_self, singleton_subset_iff, mem_inter, mem_toFinset]


lemma getVert_congr {G : SimpleGraph V}
    {a b : V} {i j : ℕ} (p : G.Walk a b) {hp : p.IsPath} {h : p.getVert i = p.getVert j}
    {hn1 : i ≤ p.length} {hn2 : j ≤ p.length} :
    i = j := by
  rw [SimpleGraph.Walk.getVert_eq_support_getElem p hn1] at h
  rw [SimpleGraph.Walk.getVert_eq_support_getElem p hn2] at h
  rw [List.Nodup.getElem_inj_iff] at h
  · omega
  · exact hp.support_nodup


lemma len_dropUntil {G : SimpleGraph V} [DecidableEq V]
  [G.LocallyFinite] {a b : V} (p : G.Walk a b) {hp : p.IsPath} {i : ℕ} {hi : p.getVert i ∈ p.support} {hn : i ≤ p.length} :
  (p.dropUntil _ hi).length = p.length - i := by
  have : (p.dropUntil _ hi).length = p.length - (p.takeUntil _ hi).length := by
    have len : p.length = (p.dropUntil _ hi).length + (p.takeUntil _ hi).length := by
      rw [add_comm]
      rw [← SimpleGraph.Walk.length_edges, ← SimpleGraph.Walk.length_edges,
        ← SimpleGraph.Walk.length_edges]
      rw [ ← List.length_append]
      conv_rhs => enter [1]; rw [← SimpleGraph.Walk.edges_append (p := p.takeUntil _ hi),
        SimpleGraph.Walk.take_spec]
    omega
  rw [this, len_takeUntil (hp := hp) (hn := hn)]

lemma len_takeUntil_reverse_takeUntil {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]
    {a b : V} {i j : ℕ} (p : G.Walk a b) {hp : p.IsPath} {hj : p.getVert j ∈ p.support} {hi : p.getVert i ∈ (p.takeUntil _ hj).reverse.support} {hn1 : j ≤ p.length} {hn2 : i ≤ j}
    : ((p.takeUntil _ hj).reverse.takeUntil _ hi).length = j - i := by
  have len_take_i : (p.takeUntil (p.getVert j) hj).length = j := by
    rw [len_takeUntil (hp := hp)]; linarith
  have l : (p.takeUntil (p.getVert j) hj).reverse.getVert (j - i) = p.getVert i := by
    rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
    rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
    · omega
    · rw [len_take_i]
      rw [Nat.sub_sub_self]
      · omega
      · omega
  rw [length_takeUntil_eq_index (p := (p.takeUntil (p.getVert j) hj).reverse)]
  conv_lhs => enter [1]; rw [← l]
  · rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
    · simp only [support_reverse, nodup_reverse]
      rw [← SimpleGraph.Walk.isPath_def]
      apply SimpleGraph.Walk.IsPath.takeUntil
      exact hp
    · rw [SimpleGraph.Walk.length_reverse, len_take_i]
      omega
  · rw [SimpleGraph.Walk.length_reverse, len_takeUntil (hp := hp)]
    · have l : (p.takeUntil (p.getVert j) hj).reverse.getVert (j - i) = p.getVert i := by
        rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
        rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
        · omega
        · rw [len_take_i]
          rw [Nat.sub_sub_self]
          · omega
          · omega
      conv_lhs => enter [1]; rw [← l]
      rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
      · omega
      · rw [← SimpleGraph.Walk.isPath_def]
        simp only [isPath_reverse_iff]
        apply SimpleGraph.Walk.IsPath.takeUntil
        exact hp
      rw [SimpleGraph.Walk.length_reverse, len_take_i]
      omega
    · linarith
  · simp only [isPath_reverse_iff]
    apply SimpleGraph.Walk.IsPath.takeUntil
    exact hp

/--
The tail of a simple path is also a simple path.
-/
lemma tail_Ispath {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) {hp : p.IsPath} {h : ¬p.Nil} : p.support.tail.Nodup := by
    rw [← SimpleGraph.Walk.support_tail_of_not_nil]
    · rw [← SimpleGraph.Walk.isPath_def]
      apply SimpleGraph.Walk.IsPath.tail
      exact hp
    · exact h


/--
The start point of path p is not in the tail of the path.
-/
lemma end_not_exsit_tail {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) {hp : p.IsPath} {h : ¬p.Nil} :
    u ∉ p.support.tail := by
  classical
  have s_eq : p.tail.support = p.support.erase u := by
    nth_rw 2 [SimpleGraph.Walk.support_eq_cons]
    rw [List.erase_cons_head, SimpleGraph.Walk.support_tail_of_not_nil]
    exact h
  rw [← SimpleGraph.Walk.support_tail_of_not_nil, s_eq]
  · have : (p.support.erase u).toFinset = p.support.toFinset.erase u := by
      ext x
      simp only [Finset.mem_erase, List.mem_toFinset]
      constructor
      · intro h
        constructor
        · intro h_eq
          rw [h_eq] at h
          rw [Nodup.mem_erase_iff] at h
          · simp_all only [ne_eq, not_true_eq_false, start_mem_support, and_true]
          · exact hp.support_nodup
        · apply List.mem_of_mem_erase
          exact h
      · intro h
        rw [Nodup.mem_erase_iff]
        · exact h
        · exact hp.support_nodup
    · by_contra h
      rw [← List.mem_toFinset, this] at h
      apply Finset.notMem_erase at h
      · exact h
  · exact h


lemma next_not_exsit_takeUntil {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]
  {u v : V} (p : G.Walk u v) {hp : p.IsPath} {j : ℕ} (h : p.getVert j ∈ p.support) (len : j < p.length) :
  ¬ p.getVert (j + 1) ∈ (p.takeUntil _ h).support := by
  by_contra Hk
  have h_indices_right : ∀ x ≤  p.length, p.getVert x ∈ (p.takeUntil _ h).support → x ≤ j  := by
    intro x h' hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
    rcases hx with ⟨k , hk, hj⟩
    rw [SimpleGraph.Walk.getVert_takeUntil] at hk
    · have len_take_j : (p.takeUntil _ h).length = j := by
        rw [len_takeUntil (hp := hp)]
        linarith
      rw [len_take_j] at hj
      rw [SimpleGraph.Walk.getVert_eq_support_getElem p h'] at hk
      have l2 : k ≤ p.length := by omega
      rw [SimpleGraph.Walk.getVert_eq_support_getElem p l2] at hk
      rw [List.Nodup.getElem_inj_iff] at hk
      · rw [hk] at hj
        · exact hj
      · exact hp.support_nodup
    · exact hj
  have l : (j + 1) ≤ p.length := by omega
  have h_contra := h_indices_right (j + 1) l Hk
  omega



lemma List_erase_toFinset [DecidableEq V] {G : SimpleGraph V} {a b : V} (p : G.Walk a b) {hp : p.IsPath} :
  (p.support.erase a).toFinset = p.support.toFinset.erase a := by
  ext x
  simp only [Finset.mem_erase, List.mem_toFinset]
  constructor
  · intro h
    constructor
    · intro h_eq
      rw [h_eq] at h
      rw [Nodup.mem_erase_iff] at h
      · simp_all
      · exact hp.support_nodup
    · apply List.mem_of_mem_erase
      exact h
  · intro h
    rw [Nodup.mem_erase_iff]
    · exact h
    · exact hp.support_nodup




lemma h_indices_trans_1 [DecidableEq V] {G : SimpleGraph V} {a b x : V} (p : G.Walk a b) {hp : p.IsPath} {i : ℕ} {h : p.getVert i ∈ p.reverse.support} {hx : x ∈ (p.reverse.takeUntil _ h).support} {len : i ≤ p.length} :
  ∃ k, p.reverse.getVert k = x ∧ k ≤ p.length - i := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
  rcases hx with ⟨k , hk, hj⟩
  rw [SimpleGraph.Walk.getVert_takeUntil] at hk
  · use k
    simp_all only [true_and]
    have l': i < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      linarith
    have : p.reverse.getVert (p.reverse.takeUntil _ h).length =
      p.reverse.getVert (p.length - i) := by
      rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
      rw [Nat.sub_sub_self]
      simp only [length_support] at l'
      linarith
    rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
    · simp only [length_support] at l'
      have l : (p.length - i) ≤ p.reverse.length := by simp
      rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l] at this
      · rw [List.Nodup.getElem_inj_iff] at this
        · simp_all only [length_support, Walk.length_reverse,
            tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
        simp only [support_reverse, nodup_reverse]
        exact hp.support_nodup
    · apply SimpleGraph.Walk.length_takeUntil_le
  · exact hj

lemma h_indices_trans_2 {G : SimpleGraph V} [G.LocallyFinite] [DecidableEq V]
  {a b x : V} (p : G.Walk a b) {i : ℕ} {hp : p.IsPath} {h : p.getVert i ∈ p.support}
  {hx : x ∈ (p.takeUntil _ h).support} {len : i ≤ p.length}
: ∃ k, p.getVert k = x ∧ k ≤ i := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
  rcases hx with ⟨k, hk, hj⟩
  rw [SimpleGraph.Walk.getVert_takeUntil] at hk
  · use k
    simp_all only [true_and]
    have : p.getVert (p.takeUntil _ h).length = p.getVert i := by
      rw [SimpleGraph.Walk.getVert_length_takeUntil]
    rw [len_takeUntil] at this
    · rw [len_takeUntil] at hj
      · exact hj
      · exact hp
      · omega
    · exact hp
    · omega
  · exact hj



lemma h_indices_trans_3 {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]
  {a b x : V} (p : G.Walk a b) {hp : p.IsPath} {i j : ℕ} {hi : p.getVert i ∈ p.support} {hn : p.getVert j ∈ (p.takeUntil _ hi).reverse.support}
  {hx : x ∈ ((p.takeUntil _ hi).reverse.takeUntil _ hn).support} {len : i ≤ p.length} {hl : j ≤ i}
: ∃ k, p.getVert (i - k) = x ∧ k ≤ i - j:= by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
  rcases hx with ⟨k , hk, hj⟩
  rw [SimpleGraph.Walk.getVert_takeUntil] at hk
  · use k
    have l : p.getVert j ∈ p.reverse.support := by
      simp only [support_reverse, mem_reverse, getVert_mem_support]
    have :  p.getVert (p.takeUntil _ hi).length = p.getVert i := by
      rw [SimpleGraph.Walk.getVert_length_takeUntil]
    obtain congr := getVert_congr (h := this) (hp := hp) (hn1 := by apply SimpleGraph.Walk.length_takeUntil_le) (hn2 := by omega)
    rw [ SimpleGraph.Walk.getVert_reverse, SimpleGraph.Walk.getVert_takeUntil, congr] at hk
    · have len : ((p.takeUntil _ hi).reverse.takeUntil _ hn).length =
        i - j := by
        have len_take_i : (p.takeUntil _ hi).length = i := by
          rw [len_takeUntil]
          · exact hp
          · omega
        have l :  (p.takeUntil _ hi).reverse.getVert (i - j) = p.getVert j := by
          rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
          rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
          · linarith
          · rw [len_take_i]
            rw [Nat.sub_sub_self]
            · linarith
            · linarith
        rw [length_takeUntil_eq_index (p := (p.takeUntil _ hi).reverse)]
        conv_lhs => enter [1]; rw [← l]
        · rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
          · simp only [support_reverse, nodup_reverse]
            rw [← SimpleGraph.Walk.isPath_def]
            apply SimpleGraph.Walk.IsPath.takeUntil
            exact hp
          · rw [SimpleGraph.Walk.length_reverse, len_take_i]
            omega
        · rw [SimpleGraph.Walk.length_reverse, congr]
          have l : (p.takeUntil _ hi).reverse.getVert (i - j) = p.getVert j := by
            rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
            rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
            · linarith
            · rw [len_take_i]
              rw [Nat.sub_sub_self]
              · linarith
              · linarith
          conv_lhs => enter [1]; rw [← l]
          rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
          · omega
          · rw [← SimpleGraph.Walk.isPath_def]; simp only [isPath_reverse_iff]
            apply SimpleGraph.Walk.IsPath.takeUntil
            exact hp
          · rw [SimpleGraph.Walk.length_reverse, len_take_i]
            omega
        · simp only [isPath_reverse_iff]
          apply SimpleGraph.Walk.IsPath.takeUntil
          exact hp
      refine ⟨hk, ?_⟩
      · rw [len] at hj
        exact hj
    · omega
  · exact hj


lemma Disjoint_tail_1 {G : SimpleGraph V} [DecidableEq V]
  {a b u v : V} (p : G.Walk a b) (s : G.Walk v u) {i : ℕ} {hp : p.IsPath} {h_inter : s.support ∩ p.support = {u}}
  {hi : p.getVert i ∈ p.support} {hu : u = p.getVert i}
: s.support.Disjoint (p.takeUntil _ hi).reverse.support.tail := by
  rw [← List.inter_eq_nil_iff_disjoint]
  rw [← List.toFinset_eq_empty_iff]
  simp only [toFinset_inter]
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
    simp only [mem_toFinset] at hx_left
    simp only [mem_toFinset] at hx_right
    have h_indices_right : ¬ x ∈ s.support := by
      by_contra H
      obtain h := List.mem_of_mem_tail hx_right
      simp only [support_reverse, mem_reverse] at h
      have innet_p : (p.takeUntil _ hi).support ⊆ p.support := by
        apply SimpleGraph.Walk.support_takeUntil_subset
      rw [List.subset_def] at innet_p
      obtain h' := innet_p h
      obtain h' := List.mem_inter_of_mem_of_mem hx_left h'
      rw [h_inter, List.singleton_eq, List.mem_singleton] at h'
      have s_eq : (u :: (p.takeUntil _ hi).reverse.support.tail) =
        (p.takeUntil _ hi).reverse.support := by
        nth_rw 2 [SimpleGraph.Walk.support_eq_cons]
        simp only [hu, support_reverse, tail_reverse]
      have l : (p.takeUntil _ hi).reverse.support.Nodup := by
        rw [← SimpleGraph.Walk.isPath_def]
        simp only [isPath_reverse_iff]
        apply SimpleGraph.Walk.IsPath.takeUntil
        exact hp
      rw [← s_eq] at l
      obtain H := List.Nodup.notMem l
      have : x ∉ (p.takeUntil _ hi).reverse.support.tail := by
        simpa [h'] using H
      contradiction
    contradiction
  · apply Finset.empty_subset


lemma Disjoint_tail_2 {G : SimpleGraph V} [DecidableEq V]
  {a b u v : V} (p : G.Walk a b) (s : G.Walk v u) {hp : p.IsPath} {i j : ℕ} {h_inter : s.support ∩ p.support = {u}} {hj : p.getVert j ∈ p.support}
  {hi : p.getVert i ∈ (p.takeUntil _ hj).reverse.support} {hu : u = p.getVert j} :
  s.support.Disjoint ((p.takeUntil _ hj).reverse.takeUntil (p.getVert _) hi).support.tail := by
  rw [← List.inter_eq_nil_iff_disjoint, ← List.toFinset_eq_empty_iff]
  simp only [toFinset_inter]
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
    simp only [mem_toFinset] at hx_left
    simp only [mem_toFinset] at hx_right
    have h_indices_right : ¬ x ∈ s.support := by
      by_contra H
      obtain h := List.mem_of_mem_tail hx_right
      have innet_p : ((p.takeUntil _ hj).reverse.takeUntil _ hi).support ⊆ p.support := by
        have inner_p : ((p.takeUntil _ hj).reverse.takeUntil _ hi).support ⊆ (p.takeUntil _ hj).reverse.support := by
          apply SimpleGraph.Walk.support_takeUntil_subset
        simp only [support_reverse, subset_reverse] at inner_p
        have outer_p : (p.takeUntil _ hj).support ⊆ p.support := by
          apply SimpleGraph.Walk.support_takeUntil_subset
        obtain h := List.Subset.trans inner_p outer_p
        exact h
      rw [List.subset_def] at innet_p
      obtain h' := innet_p h
      obtain h' := List.mem_inter_of_mem_of_mem hx_left h'
      rw [h_inter,  List.singleton_eq, List.mem_singleton] at h'
      have s_eq : (u :: ((p.takeUntil _ hj).reverse.takeUntil (p.getVert _) hi).support.tail).reverse
        = ((p.takeUntil _ hj).reverse.takeUntil (p.getVert _) hi).support.reverse := by
        nth_rw 2 [SimpleGraph.Walk.support_eq_cons]
        rw [hu]
      have l : (((p.takeUntil _ hj).reverse.takeUntil (p.getVert _) hi).support.reverse).Nodup := by
        simp only [nodup_reverse]
        rw [← SimpleGraph.Walk.isPath_def]
        apply SimpleGraph.Walk.IsPath.takeUntil
        simp only [isPath_reverse_iff]
        apply SimpleGraph.Walk.IsPath.takeUntil
        exact hp
      rw [← s_eq] at l
      rw [List.nodup_reverse] at l
      obtain  H:= List.Nodup.notMem  l
      have : x ∉ ((p.takeUntil _ hj).reverse.takeUntil (p.getVert _) hi).support.tail.reverse := by
        simpa [h'] using H
      simp only [mem_reverse] at this
      contradiction
    contradiction
  · apply Finset.empty_subset

lemma getVert_dropUntil {u v w : V} {n m : ℕ} [DecidableEq V] {G : SimpleGraph V} {p : G.Walk u v} (hw : w ∈ p.support) (hn1 : n = (p.takeUntil w hw).length) (hn1 : n ≤ p.length) :
    (p.dropUntil w hw).getVert m = p.getVert (n + m) := by
  conv_rhs => rw [← take_spec p hw, getVert_append]
  cases hn1.lt_or_eq <;> simp_all


set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option maxHeartbeats 200000000000000 in
/--
The most complex lemma in Ore's theorem: proving that
under Ore's condition, all vertices must lie on the longest path.
-/
lemma maximal_path_extends_or_hamiltonian {G : SimpleGraph V} [Fintype V] [G.LocallyFinite]
    {hG : G.Connected} {a b : V} (p : G.Walk a b) (hp : Walk.IsMaxlongPath p) {h_order : Fintype.card V ≥ 3} {h_ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ Fintype.card V} :
    ∀ v , v ∈ p.support := by
  unfold Walk.IsMaxlongPath at hp
  obtain ⟨hp_path, hp_max⟩ := hp
  intro v
  by_contra! hv_not_in_p
  obtain h_neq := endpoint_ne (p := p) (hG := hG) (hp := ⟨hp_path, hp_max⟩) (hv_not_in_p := ⟨v, hv_not_in_p⟩) (h_order := h_order)
  classical
  rcases Decidable.em (G.Adj a v) with hav | hav
  · let q : G.Walk v b := Walk.cons hav.symm p
    have hq_path : q.IsPath := by
      refine ⟨?_, ?_⟩
      · obtain h := SimpleGraph.Walk.IsPath.cons (hp := hp_path) hv_not_in_p (h := hav.symm)
        exact h.1
      · simp only [support_cons, nodup_cons, hp_path.2, and_true, q]
        omega
    have hq_length : q.length = p.length + 1 := by simp only [Walk.length_cons, q]
    have := hp_max v b q ⟨hq_path.1, ?_⟩
    · rw [hq_length] at this
      linarith
    · rw [SimpleGraph.Walk.isPath_def] at hq_path
      omega
  · rcases Decidable.em (G.Adj b v) with hbv | hbv
    · let q : G.Walk a v := p.append (.cons hbv .nil)
      have hq_path : q.IsPath := by
        unfold q
        simp_all only [ge_iff_le, ne_eq]
        rw [← SimpleGraph.Walk.concat_eq_append]
        rw [SimpleGraph.Walk.concat_isPath_iff]
        obtain h :=  SimpleGraph.Walk.IsPath.cons (hp := hp_path) (hu :=hv_not_in_p)
        refine ⟨hp_path, hv_not_in_p⟩
      have hq_length : q.length = p.length + 1 := by simp only [Walk.length_append,
        Walk.length_cons, Walk.length_nil, zero_add, q]
      have := hp_max a v q ⟨hq_path.1, ?_⟩
      · rw [hq_length] at this
        linarith
      · rw [SimpleGraph.Walk.isPath_def] at hq_path
        omega
    · let I : Finset (Fin (p.support.length - 1)) :=
        (Finset.univ : Finset (Fin (p.support.length - 1))).filter (fun i =>
          let x := p.support.get ⟨i.val + 1, by
            have := i.2
            omega⟩
          G.Adj a x)
      let J : Finset (Fin (p.support.length - 1)) :=
        (Finset.univ : Finset (Fin (p.support.length - 1))).filter (fun i =>
            let y := p.support.get ⟨i.val , by
              have := i.2
              omega⟩
            G.Adj y b )
      have disjoint : I ∩ J = ∅ := by
        have support_length : p.support.length - 1 = p.length := by
          rw [SimpleGraph.Walk.length_support, Nat.add_sub_cancel]
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        simp only [mem_inter] at hi
        rcases hi with ⟨hiI, hiJ⟩
        simp only [I, Finset.mem_filter] at hiI
        simp only [J, Finset.mem_filter] at hiJ
        have hi_val_lt : i.val + 1 < p.support.length := by omega
        let x := p.support.get ⟨i.val + 1, by
          have : i.val + 1 < p.support.length := by
            omega
          exact this⟩
        let y := p.support.get ⟨i.val , by
          have : i.val < p.support.length := by omega
          exact this⟩
        have h_adj_ax  : G.Adj a x := by
          subst x
          simp_all only [ge_iff_le, ne_eq, get_eq_getElem]
        have h_adj_yb : G.Adj y b := by
          subst y
          simp_all only [ge_iff_le, ne_eq, get_eq_getElem]
        have h_x_eq : x = p.getVert (i.val + 1) := by
          simp only [get_eq_getElem, x]
          rw [SimpleGraph.Walk.getVert_eq_support_getElem]
          have := i.2
          omega
        have h_y_eq : y = p.getVert (i.val) := by
          simp only [get_eq_getElem, y]
          rw [SimpleGraph.Walk.getVert_eq_support_getElem]
          have := i.2
          omega
        obtain H := exsist_walk (hG := hG) (p := p) (i := i) (hp := ⟨hp_path, hp_max⟩) v
        rcases H with ⟨j, h_reach_vj, s, hs_path, hs_inter⟩
        have h_x_eq : x = p.getVert (i.val + 1) := by
          simp only [get_eq_getElem, x]
          rw [SimpleGraph.Walk.getVert_eq_support_getElem]
          have := i.2
          omega
        have h1 : p.getVert j ∈ p.support := by simp only [getVert_mem_support]
        have h2 : p.getVert (i + 1) ∈ p.reverse.support := by simp only [support_reverse, mem_reverse, getVert_mem_support]
        have h3 : p.getVert i ∈ p.support := by simp only [getVert_mem_support]
        rcases Decidable.em (j + 1 ≤ i) with hji_eq | hji_ne
        · let eady_ja : G.Walk (p.getVert j) a := (p.takeUntil _ h1).reverse
          let eady_xb : G.Walk x b := ((p.reverse.takeUntil _ h2)).reverse.copy h_x_eq.symm  rfl
          let k := p.getVert (j + 1)
          let eady_ya : G.Walk y a := ((p.takeUntil _ h3).reverse.copy h_y_eq.symm rfl)
          have hj_succ : p.getVert (j + 1) ∈ eady_ya.support := by
            rw [SimpleGraph.Walk.getVert_eq_support_getElem]
            · simp only [support_copy, support_reverse, mem_reverse, eady_ya]
              have : j + 1 ≤ (i + 1) := by
                omega
              rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
              use (j + 1)
              constructor
              · rw [SimpleGraph.Walk.getVert_takeUntil]
                · rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                  have : i < p.support.length := by omega
                  simp only [length_support] at this
                  omega
                · rw [len_takeUntil (p := p) (hp := hp_path)]
                  · omega
                  · rw [← support_length]; omega
              · rw [len_takeUntil (p := p) (hp := hp_path)]
                · omega
                · rw [← support_length]; omega
            · rw [← support_length]; omega
          let eady_yjsucc := eady_ya.takeUntil (p.getVert (j + 1)) hj_succ
          let q  := eady_yjsucc.reverse.append (Walk.cons h_adj_yb (eady_xb.reverse.append (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse)))
          have hq_len : q.length = p.length + s.length:= by
            simp only [Walk.reverse_append, Walk.length_append, Walk.length_reverse, Walk.length_cons, q]
            have l1' : eady_yjsucc.length = i - (j + 1) := by
              have l2 : eady_ya.length = i := by
                simp only [length_copy, Walk.length_reverse, eady_ya]
                rw [len_takeUntil (p := p) (hp := hp_path)]
                rw [← support_length]; omega
              have h3' : p.getVert (j + 1) = eady_ya.reverse.getVert (j + 1) := by
                simp only [reverse_copy, Walk.reverse_reverse, getVert_copy, eady_ya]
                rw [SimpleGraph.Walk.getVert_takeUntil]
                simp only [length_copy, Walk.length_reverse, eady_ya] at l2
                rw [l2]
                linarith
              have h3 : p.getVert (j + 1) ∈ eady_ya.support := by
                rw [h3']
                rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                · simp only [support_reverse, getElem_reverse, length_support, add_tsub_cancel_right, getElem_mem]
                · rw [SimpleGraph.Walk.length_reverse, l2]
                  linarith
              simp only [eady_yjsucc]
              obtain H := SimpleGraph.Walk.getVert_length_takeUntil h3
              rw [SimpleGraph.Walk.getVert_eq_support_getElem] at H
              · have l : eady_yjsucc.length ≤ p.length := by
                  simp only [eady_yjsucc]
                  calc
                  _ ≤ eady_ya.length := by
                    apply SimpleGraph.Walk.length_takeUntil_le
                  _ ≤  p.length := by
                    simp only [length_copy, Walk.length_reverse, eady_ya]
                    apply SimpleGraph.Walk.length_takeUntil_le
                have : j + 1 ≤ eady_ya.reverse.length := by
                  rw [SimpleGraph.Walk.length_reverse, l2]
                  linarith
                conv at H =>
                  right; rw [h3']
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem (h := this)]; rfl
                · simp only [support_reverse, getElem_reverse, length_support,
                  add_tsub_cancel_right] at H
                  rw [List.Nodup.getElem_inj_iff]  at H
                  · rw [H, l2]
                  · simp only [support_copy, support_reverse, nodup_reverse, eady_ya]
                    rw [← SimpleGraph.Walk.isPath_def]
                    apply SimpleGraph.Walk.IsPath.takeUntil
                    exact hp_path
              · apply SimpleGraph.Walk.length_takeUntil_le
            rw [l1']
            have eady_xb_len : eady_xb.length = p.length - (i + 1) := by
              simp only [length_copy, Walk.length_reverse, eady_xb]
              rw [len_reverse_takeUntil (p := p) (hp := hp_path) (i := i + 1) (hi := h2)]
            rw [eady_xb_len]
            have eady_ja_len : eady_ja.length = j := by
              simp only [Walk.length_reverse, eady_ja]
              rw [len_takeUntil (p := p) (hp := hp_path) (i := j) (hi := h1) (hn := by omega)]
            rw [eady_ja_len, ← Nat.sub_sub, ← Nat.sub_sub, ← Nat.sub_add_comm, ← Nat.add_assoc, ← Nat.add_assoc]
            · have : 0 < p.length := by
                rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
                by_contra H
                obtain l := SimpleGraph.Walk.Nil.eq H
                contradiction
              repeat rw [← Nat.add_assoc]
              · rw [← Nat.add_comm (m := i - j),Nat.sub_right_comm, ← Nat.add_sub_assoc]
                · rw [Nat.sub_add_cancel]
                  · rw [Nat.sub_add_cancel,←  Nat.sub_add_comm]
                    · simp only [add_tsub_cancel_right]
                      rw [Nat.sub_add_cancel]
                      omega
                    · linarith
                    · have : i + 1 < p.support.length := by omega
                      simp only [length_support, add_lt_add_iff_right] at this
                      omega
                  · omega
                · linarith
            · omega
          have hq_path : q.IsPath := by
            rw [SimpleGraph.Walk.isPath_def]
            simp only [Walk.reverse_append, q]
            obtain H := List.nodup_append' (l₁ := eady_yjsucc.reverse.support) (l₂ := (Walk.cons h_adj_yb (eady_xb.reverse.append (Walk.cons h_adj_ax.symm (eady_ja.reverse.append s.reverse)))).support.tail)
            have : (eady_yjsucc.reverse.append (Walk.cons h_adj_yb (eady_xb.reverse.append (Walk.cons h_adj_ax.symm (eady_ja.reverse.append s.reverse))))).support.Nodup =
              (eady_yjsucc.reverse.support ++ (Walk.cons h_adj_yb (eady_xb.reverse.append (Walk.cons h_adj_ax.symm (eady_ja.reverse.append s.reverse)))).support.tail).Nodup  := by
              rw [Walk.support_append (p := eady_yjsucc.reverse) (p' := (Walk.cons h_adj_yb (eady_xb.reverse.append (Walk.cons h_adj_ax.symm (eady_ja.reverse.append s.reverse)))))]
            rw [this, H]
            constructor
            · simp only [takeUntil_copy, reverse_copy, support_copy, support_reverse,
              nodup_reverse, eady_yjsucc, eady_ya]
              simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons, List.tail_cons,
                nodup_reverse, disjoint_reverse_left, eq_iff_iff]
              rw [SimpleGraph.Walk.isPath_def] at hs_path
              rw [← SimpleGraph.Walk.isPath_def]
              apply SimpleGraph.Walk.IsPath.takeUntil
              apply SimpleGraph.Walk.IsPath.reverse
              apply SimpleGraph.Walk.IsPath.takeUntil
              exact hp_path
            · have H'' : (p.takeUntil (p.getVert j) h1).support.Disjoint s.reverse.support.tail := by
                rw [← List.inter_eq_nil_iff_disjoint]
                rw [← SimpleGraph.Walk.support_tail_of_not_nil]
                · have hj_in : p.getVert (j + 1) ∈ p.support := by simp only [getVert_mem_support]
                  have s_eq : s.reverse.tail.support = s.reverse.support.erase (p.getVert j) := by
                    nth_rw 2 [SimpleGraph.Walk.support_eq_cons]
                    rw [List.erase_cons_head, SimpleGraph.Walk.support_tail_of_not_nil]
                    by_contra! H
                    obtain l := SimpleGraph.Walk.Nil.eq H
                    rw [l] at h1
                    simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
                  rw [s_eq, List.inter_eq_nil_iff_disjoint, ← List.disjoint_toFinset_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
                  have : (s.reverse.support.erase (p.getVert j)).toFinset = s.reverse.support.toFinset.erase (p.getVert j) := by
                    apply List_erase_toFinset
                    simp only [isPath_reverse_iff]
                    exact hs_path
                  rw [this]
                  have h_support_eq (hs_inter : s.support ∩ p.support = {p.getVert j}):
                      s.support.toFinset ∩ p.support.toFinset = {p.getVert j} := by
                    rw [← List.toFinset_inter, hs_inter]
                    ext x
                    simp only [mem_toFinset, Finset.mem_singleton]
                    exact List.mem_singleton
                  obtain h_support_eq' := h_support_eq hs_inter
                  rw [Finset.inter_comm] at h_support_eq'
                  rw [SimpleGraph.Walk.support_reverse, List.toFinset_reverse]
                  apply Finset.Subset.antisymm
                  · have h_subset : (p.takeUntil (p.getVert j) h1).support ⊆ p.support := by
                      apply SimpleGraph.Walk.support_takeUntil_subset
                    intro x hx
                    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                    have : x ∈ p.support.toFinset ∩ s.support.toFinset := by
                      rw [Finset.mem_inter]
                      constructor
                      · simp only [mem_toFinset] at hx_left
                        rw [List.subset_def] at h_subset
                        obtain h := h_subset hx_left
                        simp only [mem_toFinset]
                        exact h
                      · simp only [mem_erase, ne_eq, mem_toFinset] at hx_right
                        simp only [mem_toFinset]
                        exact hx_right.2
                    rw [h_support_eq', Finset.mem_singleton] at this
                    rw [Finset.mem_erase] at hx_right
                    simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons, List.tail_cons,
                      nodup_reverse, disjoint_reverse_left, eq_iff_iff, getVert_mem_support,
                      toFinset_reverse, forall_const, mem_inter, mem_toFinset, end_mem_support,
                      mem_erase, not_true_eq_false, and_true, and_false]
                  · intro x hx
                    rw [Finset.mem_inter]
                    simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons, List.tail_cons,
                      nodup_reverse, disjoint_reverse_left, eq_iff_iff, getVert_mem_support,
                      toFinset_reverse, forall_const, notMem_empty]
                · simp only [nil_reverse]
                  by_contra H
                  apply SimpleGraph.Walk.Nil.eq at H
                  simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
              have H3 : eady_xb.reverse.support.Disjoint (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse).support.tail := by
                have l_nodup: (eady_xb.reverse.support ++ (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse).support.tail).Nodup := by
                  simp only [reverse_copy, Walk.reverse_reverse, support_copy, Walk.reverse_append,
                    support_cons, List.tail_cons, eady_xb, eady_ja]
                  have : ((p.takeUntil (p.getVert j) h1).append s.reverse).support.Nodup =
                        ((p.takeUntil (p.getVert j) h1).support ++ s.reverse.support.tail).Nodup  := by
                          rw [Walk.support_append]
                  rw [List.nodup_append']
                  constructor
                  · rw [← SimpleGraph.Walk.isPath_def]
                    apply SimpleGraph.Walk.IsPath.takeUntil
                    simp only [isPath_reverse_iff]
                    exact hp_path
                  · constructor
                    · rw [this, List.nodup_append']
                      constructor
                      · rw [← SimpleGraph.Walk.isPath_def]
                        apply SimpleGraph.Walk.IsPath.takeUntil
                        exact hp_path
                      · constructor
                        · simp only [support_reverse, tail_reverse, nodup_reverse]
                          have : s.support.dropLast.concat (p.getVert j) = s.support := by
                              nth_rw 2 [SimpleGraph.Walk.support_eq_concat]
                          have l : (s.support.dropLast.concat (p.getVert j)).Nodup := by
                            rw [this]
                            exact hs_path.support_nodup
                          rw [List.nodup_concat] at l
                          exact l.2
                        · omega
                    · rw [← List.inter_eq_nil_iff_disjoint]
                      rw [SimpleGraph.Walk.support_append]
                      obtain h_perm := List.Perm.inter_append H'' (l := (p.reverse.takeUntil (p.getVert (↑i + 1)) h2).support)
                      obtain h := List.toFinset_eq_of_perm (h := h_perm)
                      rw [← List.toFinset_eq_empty_iff, h]
                      simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons,
                        List.tail_cons, nodup_reverse, disjoint_reverse_left, eq_iff_iff,
                        tail_reverse, disjoint_reverse_right, inter_reverse, toFinset_inter,
                        toFinset_append, toFinset_reverse, union_eq_empty]
                      constructor
                      · apply Finset.Subset.antisymm
                        · intro x hx
                          rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                          simp only [mem_toFinset] at hx_left
                          simp only [mem_toFinset] at hx_right
                          have h_indices_left : ∃ k, p.reverse.getVert k = x ∧ k ≤ p.length - (i + 1) := by
                            obtain H := h_indices_trans_1 (hp := hp_path) (hx := hx_left) (i := i + 1) (h := h2) (len := by omega)
                            apply H
                          have h_indices_right : ∃ k, p.getVert k = x ∧ k ≤ j := by
                            obtain H := h_indices_trans_2 (hp := hp_path) (hx := hx_right) (i := j) (h := h1) (len := by omega)
                            apply H
                          rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                          rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                          rw [SimpleGraph.Walk.getVert_reverse] at hk₁_eq
                          rw [← hk₂_eq] at hk₁_eq
                          have hk_eq : k₁ = p.length - k₂ := by
                            obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                            rw [← congr, Nat.sub_sub_self]
                            omega
                          rw [hk_eq] at hk₁_ge
                          have hj_lt_i : k₂ ≥  i + 1 := by
                            rw [tsub_le_tsub_iff_left] at hk₁_ge
                            · omega
                            · have l': i + 1 < p.support.length := by
                                omega
                              simp only [length_support, add_lt_add_iff_right] at l'
                              linarith
                          linarith [hk₁_ge, hk₂_le]
                        · intro x hx
                          simp_all only [notMem_empty]
                      · apply Finset.Subset.antisymm
                        · intro x hx
                          rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                          simp only [mem_toFinset] at hx_left
                          simp only [mem_toFinset] at hx_right
                          by_contra! H
                          have h1 : x ∈ s.support := by
                            obtain := List.mem_of_mem_dropLast hx_right
                            omega
                          have h2 : x ∈ p.support := by
                            rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
                            rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                            rcases hx_left with ⟨n ,h1, h2⟩
                            use (p.length - n)
                            rw [SimpleGraph.Walk.getVert_takeUntil, SimpleGraph.Walk.getVert_reverse] at h1
                            · refine ⟨h1, by omega⟩
                            · exact h2
                          have h3 : x = p.getVert j := by
                            have h_inter : x ∈ s.support ∩ p.support := by
                              simp only [mem_inter_iff]
                              refine ⟨h1, h2⟩
                            rw [hs_inter, List.singleton_eq] at h_inter
                            simp_all only [mem_inter, mem_toFinset, and_self, notMem_empty,
                              not_false_eq_true, List.mem_cons, not_mem_nil, or_false]
                          have h4 : ¬ p.getVert j ∈ s.support.dropLast := by
                            have : s.support.dropLast.concat (p.getVert j) = s.support := by
                              nth_rw 2 [SimpleGraph.Walk.support_eq_concat]
                            have l : (s.support.dropLast.concat (p.getVert j)).Nodup := by
                              rw [this]
                              exact hs_path.support_nodup
                            rw [List.nodup_concat] at l
                            exact l.1
                          have : x ∉ s.support.dropLast := by
                            simpa [h3] using h4
                          simp_all only [length_support, add_tsub_cancel_right, mem_inter,
                            mem_toFinset, and_false]
                        · apply Finset.empty_subset
                simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons, List.tail_cons,
                  nodup_reverse, disjoint_reverse_left, eq_iff_iff, tail_reverse,
                  disjoint_reverse_right, Walk.reverse_append]
                obtain H := List.nodup_append'  (l₁ := eady_xb.reverse.support) (l₂ := (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse).support.tail)
                simp only [support_reverse, Walk.reverse_append, support_cons, List.tail_cons,
                  nodup_reverse, disjoint_reverse_left] at H
                rw [H] at l_nodup
                simp_all only [and_self, iff_true]
              constructor
              · simp only [support_cons, List.tail_cons]
                rw [SimpleGraph.Walk.isPath_def] at hs_path
                have : ((eady_xb.reverse.append (Walk.cons h_adj_ax.symm (eady_ja.reverse.append s.reverse)))).support.Nodup =
                    (eady_xb.reverse.support ++ (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse).support.tail).Nodup  := by
                  rw [Walk.support_append]
                  simp only [support_reverse, support_cons, List.tail_cons, Walk.reverse_append]
                obtain H := List.nodup_append' (l₁ := eady_xb.reverse.support) (l₂ := (Walk.cons h_adj_ax.symm (s.append eady_ja).reverse).support.tail)
                rw [this, H]
                constructor
                · simp only [reverse_copy, Walk.reverse_reverse, support_copy, eady_xb]
                  rw [← SimpleGraph.Walk.isPath_def]
                  apply SimpleGraph.Walk.IsPath.takeUntil
                  simp only [isPath_reverse_iff]
                  exact hp_path
                · constructor
                  · simp only [Walk.reverse_append, support_cons, List.tail_cons]
                    have : (eady_ja.reverse.append s.reverse).support.Nodup =
                    (eady_ja.reverse.support ++ s.reverse.support.tail).Nodup  := by
                      rw [Walk.support_append]
                    obtain H := List.nodup_append' (l₁ := eady_ja.reverse.support) (l₂ := s.reverse.support.tail)
                    rw [this, H]
                    constructor
                    · simp only [Walk.reverse_reverse, eady_ja]
                      rw [← SimpleGraph.Walk.isPath_def]
                      apply SimpleGraph.Walk.IsPath.takeUntil
                      exact hp_path
                    · constructor
                      · apply tail_Ispath
                        · apply SimpleGraph.Walk.IsPath.reverse
                          rw [← SimpleGraph.Walk.isPath_def] at hs_path
                          · exact hs_path
                        · simp_all only [ge_iff_le, ne_eq, support_reverse, support_cons,
                          List.tail_cons, nodup_reverse, Walk.reverse_append, disjoint_reverse_left,
                          eq_iff_iff, tail_reverse, disjoint_reverse_right, and_true, nil_reverse]
                          by_contra! H
                          obtain l := SimpleGraph.Walk.Nil.eq H
                          simp_all only [not_true_eq_false]
                      · simp only [Walk.reverse_reverse, eady_ja]
                        omega
                  · exact H3
              · have h_jsucc : p.getVert (j + 1) ∈ (p.takeUntil _ h3).reverse.support := by
                  simp only [support_reverse, mem_reverse]
                  have eq : p.getVert (j + 1) = (p.takeUntil _ h3).getVert (j + 1) := by
                    rw [SimpleGraph.Walk.getVert_takeUntil]
                    rw [len_takeUntil (p := p) (hp := hp_path)]
                    · linarith
                    · omega
                  rw [eq]
                  apply SimpleGraph.Walk.getVert_mem_support
                have eq : (eady_ja.reverse.append s.reverse) = (s.append eady_ja).reverse := by
                  rw [SimpleGraph.Walk.reverse_append]
                rw [eq, ← List.inter_eq_nil_iff_disjoint]
                simp only [support_reverse, Walk.reverse_append, support_cons, List.tail_cons]
                rw [SimpleGraph.Walk.support_append,eq]
                obtain h_perm := List.Perm.inter_append H3 (l := eady_yjsucc.support.reverse)
                obtain h := List.toFinset_eq_of_perm (h := h_perm)
                rw [← List.toFinset_eq_empty_iff, h]
                simp only [takeUntil_copy, support_copy, reverse_copy, Walk.reverse_reverse,
                  Walk.reverse_append, support_cons, List.tail_cons, toFinset_append,
                  toFinset_inter, toFinset_reverse, union_eq_empty, eady_yjsucc, eady_xb, eady_ya]
                constructor
                · apply Finset.Subset.antisymm
                  · intro x hx
                    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                    simp only [mem_toFinset] at hx_left
                    simp only [mem_toFinset] at hx_right
                    have h_indices_right : ∃ k, p.reverse.getVert k = x ∧ k ≤ p.length - (i + 1) := by
                      obtain H := h_indices_trans_1 (hp := hp_path) (hx := hx_right) (i := i + 1) (h := h2) (len := by omega)
                      apply H
                    have h_indices_left : ∃ k, p.getVert (i - k) = x ∧ k ≤ i - (j + 1)  := by
                      simp only [support_copy, eady_ya] at hj_succ
                      obtain H := h_indices_trans_3 (hp := hp_path) (hx := hx_left) (i := i) (j := j + 1) (hn := hj_succ) (len := by omega) (hl := by linarith)
                      apply H
                    rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                    rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                    rw [SimpleGraph.Walk.getVert_reverse] at hk₂_eq
                    rw [← hk₂_eq] at hk₁_eq
                    have hk_eq : i - k₁ = p.length - k₂ := by
                      obtain congr := getVert_congr (h := hk₁_eq) (hn2 := by omega) (hp := hp_path) (hn1 := by omega)
                      exact congr
                    have hk₁_ge : k₂ = p.length - (i - k₁) := by omega
                    rw [hk₁_ge] at hk₂_le
                    omega
                  · apply Finset.empty_subset
                · apply Finset.Subset.antisymm
                  · intro x hx
                    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                    simp only [Walk.reverse_reverse, mem_toFinset, mem_support_append_iff,
                      support_reverse, mem_reverse, eady_ja] at hx_right
                    simp only [mem_toFinset] at hx_left
                    have h_indices_left : ∃ k, p.getVert (i - k) = x ∧ k ≤ i - (j + 1)  := by
                      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                      rcases hx_left with ⟨k , hk, hj⟩
                      rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                      · use k
                        have l : p.getVert j ∈ p.reverse.support := by
                          simp only [support_reverse, mem_reverse, getVert_mem_support]
                        have :  p.getVert (p.takeUntil _ h3).length = p.getVert i := by
                          rw [SimpleGraph.Walk.getVert_length_takeUntil]
                        obtain congr := getVert_congr (h := this) (hn2 := by omega) (hp := hp_path) (hn1 := by apply SimpleGraph.Walk.length_takeUntil_le)
                        rw [ SimpleGraph.Walk.getVert_reverse, SimpleGraph.Walk.getVert_takeUntil, congr] at hk
                        · have len : ((p.takeUntil _ h3).reverse.takeUntil _ h_jsucc).length = i - (j + 1) := by
                            have len_take_i : (p.takeUntil _ h3).length = i := by
                              rw [len_takeUntil (hp := hp_path)]
                              omega
                            have l : (p.takeUntil _ h3).reverse.getVert (i - (j + 1)) = p.getVert (j + 1) := by
                              rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
                              rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
                              · linarith
                              · rw [len_take_i]
                                rw [Nat.sub_sub_self]
                                · linarith
                                · linarith
                            rw [length_takeUntil_eq_index (p := (p.takeUntil _ h3).reverse)]
                            conv_lhs => enter [1]; rw [← l]
                            · rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
                              · simp only [support_reverse, nodup_reverse]
                                rw [← SimpleGraph.Walk.isPath_def]
                                apply SimpleGraph.Walk.IsPath.takeUntil
                                exact hp_path
                              · rw [SimpleGraph.Walk.length_reverse, len_take_i]
                                omega
                            · rw [SimpleGraph.Walk.length_reverse, congr]
                              have l : (p.takeUntil _ h3).reverse.getVert (i - (j + 1))
                                    = p.getVert (j + 1) := by
                                rw [SimpleGraph.Walk.getVert_reverse, len_take_i]
                                rw [SimpleGraph.Walk.getVert_takeUntil, Nat.sub_sub_self]
                                · linarith
                                · rw [len_take_i]
                                  rw [Nat.sub_sub_self]
                                  · linarith
                                  · linarith
                              conv_lhs => enter [1]; rw [← l]
                              rw [SimpleGraph.Walk.getVert_eq_support_getElem, List.Nodup.idxOf_getElem]
                              · omega
                              · rw [← SimpleGraph.Walk.isPath_def];
                                simp only [isPath_reverse_iff]
                                apply SimpleGraph.Walk.IsPath.takeUntil
                                exact hp_path
                              · rw [SimpleGraph.Walk.length_reverse, len_take_i]
                                omega
                            · simp only [isPath_reverse_iff]
                              apply SimpleGraph.Walk.IsPath.takeUntil
                              exact hp_path
                          refine ⟨hk, ?_⟩
                          · rw [len] at hj
                            exact hj
                        · omega
                      · exact hj
                    rcases hx_right with (hx_right | hx_right)
                    · have h_indices_right : ∃ k, p.getVert k = x ∧ k ≤ j := by
                        have hj_le : j < p.support.length := by
                          omega
                        simp only [length_support, Order.lt_add_one_iff] at hj_le
                        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_right
                        rcases hx_right with ⟨k , hk, hj⟩
                        rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                        · use k
                          have len_take_j : (p.takeUntil _ h1).length = j := by
                            rw [len_takeUntil (hp := hp_path)]; omega
                          rw [len_take_j] at hj
                          refine ⟨hk, hj⟩
                        · exact hj
                      rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                      rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                      rw [← hk₁_eq] at hk₂_eq
                      have hk_eq : i - k₁ =  k₂ := by
                          obtain congr := getVert_congr (h := hk₂_eq) (hn2 := by omega) (hp := hp_path) (hn1 := by omega)
                          rw [congr] at hk₂_eq; linarith
                      omega
                    · by_contra H
                      have hx_left : x ∈ p.support := by
                        have : ((p.takeUntil _ h3).reverse.takeUntil _ h_jsucc).support ⊆ (p.takeUntil _ h3).reverse.support := by
                          apply SimpleGraph.Walk.support_takeUntil_subset
                        simp only [support_reverse, subset_reverse] at this
                        rw [List.subset_def] at this
                        obtain h := this hx_left
                        have l : (p.takeUntil _ h3).support ⊆ p.support := by
                          apply SimpleGraph.Walk.support_takeUntil_subset
                        rw [List.subset_def] at l
                        obtain h := l h
                        omega
                      obtain h := List.mem_inter_of_mem_of_mem  hx_right hx_left
                      rw [hs_inter, List.singleton_eq, List.mem_singleton] at h
                      rcases h_indices_left with ⟨k, h1, h2⟩
                      rw [h] at h1
                      obtain congr := getVert_congr (h := h1) (hn2 := by omega) (hp := hp_path) (hn1 := by omega)
                      omega
                  · apply Finset.empty_subset
          have : q.length > p.length := by
            rw [hq_len]
            have : 0 < s.length := by
              rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
              by_contra! H
              obtain l := SimpleGraph.Walk.Nil.eq H
              simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
            linarith
          have h_max := hp_max (p.getVert (j + 1)) v q hq_path
          rw [hq_len] at h_max
          linarith
        · have hji_ne : j + 1 > i := by omega
          rcases Decidable.em (j < p.length) with hJ | hJ
          · have h_in_i : p.getVert i ∈ p.support := by simp
            have h2 : p.getVert (j + 1) ∈ p.support := by simp only [getVert_mem_support]
            have h_in_isucc : p.getVert (i + 1) ∈ p.support := by simp
            rcases Decidable.em (i = j) with hI | hI
            · have eq : p.getVert i = p.getVert j := by simp only [hI]
              have h_pen_in : p.penultimate ∈ p.support := by simp
              let eady_ja : G.Walk (p.getVert j) a := (p.takeUntil _ h_in_i).reverse.copy eq rfl
              let eady_v_isucc : G.Walk v (p.getVert (i + 1)) := ((s.append eady_ja).concat h_adj_ax).copy rfl h_x_eq
              let eady_isucc_b : G.Walk (p.getVert (i + 1)) b := p.dropUntil _ h_in_isucc
              let q : G.Walk v b :=  eady_v_isucc.append eady_isucc_b
              obtain h := hp_max v b q
              have hq_path : q.IsPath := by
                unfold q
                rw [SimpleGraph.Walk.isPath_def]
                obtain H := List.nodup_append'  (l₁ := eady_v_isucc.support) (l₂ := eady_isucc_b.support.tail)
                have : (eady_v_isucc.append eady_isucc_b).support.Nodup =
                  (eady_v_isucc.support ++ eady_isucc_b.support.tail).Nodup  := by
                  rw [Walk.support_append]
                rw [this, H]
                have H_x_not_in : x ∉ (p.takeUntil _ h_in_i).support := by
                    by_contra h_in_p
                    have innet_p : (p.takeUntil _ h_in_i).support ⊆ p.support := by
                      apply SimpleGraph.Walk.support_takeUntil_subset
                    rw [List.subset_def] at innet_p
                    obtain h' := innet_p h_in_p
                    have h_in : ∃ k, p.getVert k = x ∧ k ≤ i := by
                      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h_in_p
                      rcases h_in_p with ⟨k , hk, hj⟩
                      rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                      · use k
                        have len : (p.takeUntil _ h_in_i).length = i := by
                          rw [len_takeUntil (hp := hp_path)]; linarith
                        rw [len] at hj
                        refine ⟨hk, hj⟩
                      · exact hj
                    rcases h_in with ⟨k, hk_eq, hk_le⟩
                    rw [h_x_eq] at hk_eq
                    obtain congr := getVert_congr (h := hk_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                    rw [congr] at hk_eq; omega
                have len_take_isucc : (p.takeUntil _ h_in_isucc).length = i + 1 := by
                  rw [len_takeUntil (hp := hp_path)]; linarith
                have len_drop_isucc : (p.dropUntil _ h_in_isucc).length = p.length - (i + 1) := by
                  rw [len_dropUntil (hp := hp_path) (hn := by linarith)]
                constructor
                · simp only [support_copy, support_concat, List.concat_eq_append, eady_v_isucc]
                  rw [List.nodup_append']
                  constructor
                  · obtain H := List.nodup_append' (l₁ := s.support) (l₂ := eady_ja.support.tail)
                    have : (s.append eady_ja).support.Nodup = (s.support ++ eady_ja.support.tail).Nodup  := by
                      rw [Walk.support_append]
                    rw [this, H]
                    constructor
                    · exact hs_path.support_nodup
                    · constructor
                      · apply tail_Ispath
                        · simp only [eady_ja]
                          simp only [isPath_copy, isPath_reverse_iff]
                          apply SimpleGraph.Walk.IsPath.takeUntil
                          exact hp_path
                        · simp only [nil_copy, nil_reverse, nil_takeUntil, eady_ja]
                          by_contra! H
                          rw [← h_y_eq] at H
                          rw [← H] at h_adj_yb
                          obtain h' := ore_endpoints_adjacent hG ⟨hp_path, hp_max⟩ (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                          contradiction
                      · have H1 : s.support.Disjoint eady_ja.support.tail := by
                          have h' : eady_ja.getVert i ∈ eady_ja.support := by
                            simp only [support_copy,getVert_copy, eady_ja]
                            apply getVert_mem_support
                          simp only [support_copy, eady_ja]
                          obtain H := Disjoint_tail_1 (u := p.getVert j) (hp := hp_path) (s := s) (p := p) (hu := eq.symm) (h_inter := hs_inter)
                          apply H
                        exact H1
                  · constructor
                    · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
                    · simp only [List.disjoint_singleton, mem_support_append_iff, not_or]
                      constructor
                      · simp only [h_x_eq]
                        by_contra h_in_s
                        obtain h' := List.mem_inter_of_mem_of_mem h_in_s h_in_isucc
                        rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                        obtain congr := getVert_congr (h := h') (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                        omega
                      · simp only [support_copy, support_reverse, mem_reverse, eady_ja]
                        exact H_x_not_in
                constructor
                · apply tail_Ispath
                  · simp only [eady_isucc_b]
                    apply SimpleGraph.Walk.IsPath.dropUntil
                    exact hp_path
                  · simp only [eady_isucc_b]
                    by_contra h
                    obtain l := SimpleGraph.Walk.Nil.eq (p := (p.dropUntil _ h_in_isucc))
                    simp_all only [ge_iff_le, ne_eq, length_support, add_tsub_cancel_right,
                      get_eq_getElem, true_and, mem_univ, getVert_mem_support, support_reverse,
                      mem_reverse, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
                      not_false_eq_true, gt_iff_lt, lt_add_iff_pos_right, _root_.zero_lt_one,
                      implies_true, eq_iff_iff, forall_const]
                    rw [← hI] at l
                    rw [h_x_eq, l] at h_adj_ax
                    obtain h' := ore_endpoints_adjacent hG  ⟨hp_path, hp_max⟩ (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                    contradiction
                · have H2 : eady_v_isucc.support.Disjoint eady_isucc_b.support.tail := by
                    simp only [support_copy, support_concat, List.concat_eq_append,
                      disjoint_append_left, singleton_disjoint, eady_v_isucc, eady_isucc_b]
                    rw [← List.inter_eq_nil_iff_disjoint]
                    rw [← List.toFinset_eq_empty_iff]
                    simp only [toFinset_inter]
                    constructor
                    · apply Finset.Subset.antisymm
                      · intro x hx
                        rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                        simp only [mem_toFinset, mem_support_append_iff] at hx_left
                        simp only [mem_toFinset] at hx_right
                        have h : (p.dropUntil _ h_in_isucc).support.tail ⊆ (p.dropUntil _ h_in_isucc).support := by
                          apply List.tail_subset
                        have innet_p : (p.dropUntil _ h_in_isucc).support ⊆ p.support := by
                          apply SimpleGraph.Walk.support_dropUntil_subset
                        rw [List.subset_def] at h
                        obtain h' := h hx_right
                        have h_indices_right : ∃ k, p.getVert k = x ∧ k ≥ i + 1 ∧ k ≤ p.length := by
                          rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h'
                          rcases h' with ⟨k , hk, hj⟩
                          rw [getVert_dropUntil (n := i + 1)] at hk
                          · use (i + 1 + k)
                            refine ⟨hk, by simp, ?_⟩
                            simp only [len_drop_isucc] at hj
                            omega
                          · exact len_take_isucc.symm
                          · rw [← hI] at hJ
                            omega
                        rcases hx_left with (hx_left| hx_left)
                        · rcases h_indices_right with ⟨k, hk_eq, hk_ge⟩
                          obtain h := List.mem_of_mem_tail hx_right
                          have innet_p : (p.dropUntil _ h_in_isucc).support ⊆ p.support := by
                            apply SimpleGraph.Walk.support_dropUntil_subset
                          have outer_p : (p.dropUntil _ h_in_isucc).support.tail ⊆ (p.dropUntil _ h_in_isucc).support := by
                            apply List.tail_subset
                          obtain h1 := List.Subset.trans outer_p innet_p
                          rw [List.subset_def] at innet_p
                          obtain h' := innet_p h
                          obtain h' := List.mem_inter_of_mem_of_mem hx_left h'
                          rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                          rw [← hk_eq] at h'
                          obtain congr := getVert_congr (h := h') (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                          rw [congr] at h'; omega
                        · simp only [support_copy, support_reverse, mem_reverse,
                          eady_ja] at hx_left
                          have h_indices_left : ∃ k, p.getVert k = x ∧ k ≤ i := by
                            rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                            rcases hx_left with ⟨k , hk, hj⟩
                            rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                            · use k
                              rw [len_takeUntil p (hp := hp_path) (hn := by omega)] at hj
                              refine ⟨hk, hj⟩
                            · exact hj
                          rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_le⟩
                          rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_ge⟩
                          rw [← hk₁_eq] at hk₂_eq
                          obtain congr := getVert_congr (h := hk₂_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                          rw [congr] at hk₂_ge; omega
                      · apply Finset.empty_subset
                    · by_contra hx_right'
                      obtain h := List.mem_of_mem_tail hx_right'
                      have innet_p : (p.dropUntil _ h_in_isucc).support.tail ⊆ (p.dropUntil _ h_in_isucc).support := by
                        apply List.tail_subset
                      rw [List.subset_def] at innet_p
                      obtain hx_right := innet_p hx_right'
                      have p_tail_erase_eq : (p.dropUntil _ h_in_isucc).support.tail
                        = (p.dropUntil _ h_in_isucc).support.erase (p.getVert (i + 1)) := by
                        conv_rhs => rw [SimpleGraph.Walk.support_eq_cons, List.erase_cons_head]
                      rw [p_tail_erase_eq] at hx_right'
                      rw [Nodup.mem_erase_iff] at hx_right'
                      · rw [h_x_eq] at hx_right'
                        simp only [ne_eq, not_true_eq_false, start_mem_support, and_true] at hx_right'
                      · rw [← SimpleGraph.Walk.isPath_def]
                        apply SimpleGraph.Walk.IsPath.dropUntil
                        exact hp_path
                  exact H2
              · obtain h := h hq_path
                have hq_len : q.length = p.length +  s.length:= by
                  simp only [Walk.length_append, q]
                  simp only [length_copy, Walk.length_concat, Walk.length_append,
                    Walk.length_reverse, eady_v_isucc, eady_ja, eady_isucc_b]
                  rw [len_takeUntil (hp := hp_path), len_dropUntil (hp := hp_path), Nat.add_assoc (n := s.length), ← Nat.add_sub_assoc, Nat.sub_add_comm, Nat.add_sub_cancel]
                  · linarith
                  · linarith
                  · linarith
                  · linarith
                  · linarith
                have : q.length > p.length := by
                  rw [hq_len]
                  simp only [gt_iff_lt, lt_add_iff_pos_right]
                  rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
                  by_contra! H
                  obtain l := SimpleGraph.Walk.Nil.eq H
                  simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
                linarith
            · have h_in_i_succ : p.getVert (i + 1) ∈ (p.takeUntil _ h1).reverse.support := by
                simp only [support_reverse, mem_reverse]
                have : j ≥ (i + 1) := by omega
                rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
                use (i + 1)
                constructor
                · rw [SimpleGraph.Walk.getVert_takeUntil]
                  rw [len_takeUntil (hp := hp_path)]
                  · linarith
                  · linarith
                · rw [len_takeUntil (hp := hp_path)]
                  · linarith
                  · linarith
              have h2' : p.getVert (j + 1) ∈  p.reverse.support := by
                simp only [support_reverse, mem_reverse, getVert_mem_support]
              let eady_j_isucc : G.Walk (p.getVert j) x := ((p.takeUntil _ h1).reverse.takeUntil _ h_in_i_succ).copy rfl h_x_eq.symm
              let eady_va : G.Walk v a := (s.append eady_j_isucc).concat h_adj_ax.symm
              let eady_ab : G.Walk a b := ((p.takeUntil _ h_in_i).copy rfl h_y_eq.symm).concat h_adj_yb
              let eady_b_jsucc : G.Walk b (p.getVert (j + 1)) := p.reverse.takeUntil _ h2'
              let eady_bj_succ : G.Walk b (p.getVert (j + 1)) := (p.reverse.takeUntil _ h2')
              let q :  G.Walk v (p.getVert (j + 1)) :=  (eady_va.append eady_ab).append eady_bj_succ
              obtain h := hp_max v (p.getVert (j + 1))  q
              have hq_path : q.IsPath := by
                unfold q
                have Disjoint_s_j_isucc : s.support.Disjoint eady_j_isucc.support.tail := by
                  simp only [support_copy, eady_j_isucc]
                  obtain H := Disjoint_tail_2 (u := p.getVert j) (s := s) (p := p) (hp := hp_path) (h_inter := hs_inter) (hu := by rfl)
                  apply H
                rw [SimpleGraph.Walk.isPath_def]
                obtain H := List.nodup_append' (l₁ := (eady_va.append eady_ab).support) (l₂ := eady_bj_succ.support.tail)
                have : ((eady_va.append eady_ab).append eady_bj_succ).support.Nodup =
                  ((eady_va.append eady_ab).support ++ eady_bj_succ.support.tail).Nodup  := by
                  rw [Walk.support_append]
                rw [this, H]
                have Disjoint_take_i_b : b ∉ (p.takeUntil _ h_in_i).support.tail := by
                  by_contra H'
                  have trans :  ∃ k, p.getVert k = b ∧ k ≤ i := by
                    have h : (p.takeUntil _ h_in_i).support.tail ⊆ (p.takeUntil _ h_in_i).support := by
                      apply List.tail_subset
                    rw [List.subset_def] at h
                    obtain H := h H'
                    obtain H := h_indices_trans_2 (hp := hp_path) (hx := H) (i := i) (h := h3) (len := by omega)
                    exact H
                  rcases trans with ⟨k, ⟨h1, h2⟩⟩
                  have eq : b = p.getVert p.length := by simp only [getVert_length]
                  conv at h1 =>
                    right; rw [eq]
                  obtain congr := getVert_congr (h := h1) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                  omega
                have not_exist_b_take_reverse : ¬ b ∈ ((p.takeUntil _ h1).reverse.takeUntil _ h_in_i_succ).support := by
                  by_contra H
                  have h_in : ∃ k, p.getVert k = b ∧ k ≥ i + 1 ∧ k ≤ j := by
                    obtain H := h_indices_trans_3 (hp := hp_path) (hx := H) (i := j) (j := i + 1) (hn := h_in_i_succ) (len := by omega) (hl := by omega)
                    rcases H with ⟨k , hk, hj⟩
                    use j - k
                    refine ⟨hk, ?_, by simp⟩
                    omega
                  rcases h_in with ⟨k, h1, h2⟩
                  have eq : b = p.getVert p.length := by simp
                  conv at h1 => right; rw [eq]
                  obtain congr := getVert_congr (h := h1) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                  omega
                have s_append_jisucc_Disjoint : (s.append eady_j_isucc).support.Disjoint (p.takeUntil _ h_in_i).support.tail := by
                  rw [← List.inter_eq_nil_iff_disjoint, ← List.toFinset_eq_empty_iff]
                  simp only [toFinset_inter]
                  have h : (p.takeUntil _ h_in_i).support.tail ⊆ (p.takeUntil _ h_in_i).support := by
                    apply List.tail_subset
                  rw [List.subset_def] at h
                  apply Finset.Subset.antisymm
                  · intro x hx
                    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                    simp only [mem_toFinset, mem_support_append_iff] at hx_left
                    simp only [mem_toFinset] at hx_right
                    obtain H := h hx_right
                    have h_indices_right : ∃ k, p.getVert k = x ∧ k ≤ i := by
                      obtain H := h_indices_trans_2 (hp := hp_path) (hx := H) (i := i) (h := h_in_i) (len := by omega)
                      exact H
                    rcases hx_left with (hx_left | hx_left)
                    · have h : (p.takeUntil _ h_in_i).support.tail ⊆ (p.takeUntil _ h_in_i).support := by
                        apply List.tail_subset
                      rw [List.subset_def] at h
                      obtain H := h hx_right
                      have h2 : x ∈ p.support := by
                        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
                        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at H
                        rcases H with ⟨k , hk, hj⟩
                        rw [SimpleGraph.Walk.getVert_takeUntil] at hk
                        · obtain l :=  SimpleGraph.Walk.length_takeUntil_le p h_in_i
                          use k
                          refine ⟨hk, by omega⟩
                        · exact hj
                      have h3 : x = p.getVert j := by
                        have h_inter : x ∈ s.support ∩ p.support := by
                          simp only [mem_inter_iff]
                          refine ⟨hx_left, h2⟩
                        rw [hs_inter, List.singleton_eq] at h_inter
                        simp_all only [ge_iff_le, ne_eq, not_le, gt_iff_lt,
                          getVert_mem_support, implies_true, and_self,
                          eq_iff_iff, mem_inter, mem_toFinset,
                          mem_support_append_iff, true_or, List.mem_cons, not_mem_nil,
                          or_false]
                      rcases h_indices_right with ⟨k₁, hk₁_eq, hk₁_ge⟩
                      rw [h3] at hk₁_eq
                      obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                      omega
                    · simp only [support_copy, eady_j_isucc] at hx_left
                      have h_in : ∃ k, p.getVert k = x ∧ k ≥ i + 1 ∧ k ≤ j := by
                        obtain hx_left := h_indices_trans_3 (hp := hp_path) (hx := hx_left) (i := j) (j := i + 1) (hn := h_in_i_succ) (len := by omega) (hl := by omega)
                        rcases hx_left with ⟨k , hk, hj⟩
                        use j - k
                        refine ⟨hk, by omega, by omega⟩
                      rcases h_in with ⟨k₁, hk₁_eq, hk₁_ge⟩
                      rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                      rw [← hk₂_eq] at hk₁_eq
                      obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                      omega
                  · apply Finset.empty_subset
                have not_exist_take_i : a ∉ (p.takeUntil _ h_in_i).support.tail  := by
                  apply end_not_exsit_tail
                  · apply SimpleGraph.Walk.IsPath.takeUntil
                    exact hp_path
                  · simp only [nil_takeUntil]
                    by_contra H
                    have eq : a = p.getVert 0 := by simp
                    conv at H => lhs; rw [eq]
                    obtain congr := getVert_congr (h := H) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                    rw [← congr] at h_y_eq
                    simp only [h_y_eq, getVert_zero] at h_adj_yb
                    obtain no_adj := ore_endpoints_adjacent hG (hp := ⟨hp_path, hp_max⟩) (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                    contradiction
                have not_exist_s : b ∉ s.support := by
                  by_contra hb
                  have h2 : b ∈ p.support := by simp only [end_mem_support]
                  have h3 : b = p.getVert j := by
                    have h_inter : b ∈ s.support ∩ p.support := by
                      simp only [mem_inter_iff, end_mem_support, and_true]
                      exact hb
                    rw [hs_inter, List.singleton_eq] at h_inter
                    simp_all only [ge_iff_le, ne_eq, not_le, gt_iff_lt,
                      getVert_mem_support, implies_true, eq_iff_iff, end_mem_support,
                      List.mem_cons, not_mem_nil, or_false]
                  have h4 : ¬ p.getVert j ∈ s.support.dropLast := by
                    have : s.support.dropLast.concat (p.getVert j) = s.support := by
                      nth_rw 2 [SimpleGraph.Walk.support_eq_concat]
                    have l : (s.support.dropLast.concat (p.getVert j)).Nodup := by
                      rw [this]
                      exact hs_path.support_nodup
                    rw [List.nodup_concat] at l
                    exact l.1
                  have : p.getVert p.length = b := by simp only [getVert_length]
                  conv at h3 => lhs; rw [← this]
                  obtain congr := getVert_congr (h := h3) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                  omega
                rcases Decidable.em (eady_bj_succ.Nil) with h_nil | h_nil
                · constructor
                  · obtain H := List.nodup_append' (l₁ := eady_va.support) (l₂ := eady_ab.support.tail)
                    have : (eady_va.append eady_ab).support.Nodup = (eady_va.support ++ eady_ab.support.tail).Nodup := by
                      rw [Walk.support_append]
                    rw [this, H]
                    constructor
                    · simp only [support_concat, List.concat_eq_append, eady_va]
                      rw [List.nodup_append']
                      constructor
                      · obtain H := List.nodup_append'  (l₁ := s.support) (l₂ := eady_j_isucc.support.tail)
                        have : (s.append eady_j_isucc).support.Nodup = (s.support ++ eady_j_isucc.support.tail).Nodup  := by
                          rw [Walk.support_append]
                        rw [this, H]
                        have eady_j_isucc_tail_Nodup : eady_j_isucc.support.tail.Nodup := by
                          rcases Decidable.em (eady_j_isucc.Nil) with h_nil | h_nil
                          · rw [SimpleGraph.Walk.nil_iff_support_eq] at h_nil
                            simp only [h_nil, List.tail_cons, nodup_nil]
                          · simp only [support_copy, eady_j_isucc]
                            apply tail_Ispath
                            · apply SimpleGraph.Walk.IsPath.takeUntil
                              simp only [isPath_reverse_iff]
                              apply SimpleGraph.Walk.IsPath.takeUntil
                              exact hp_path
                            · simp only [nil_copy, nil_takeUntil, eady_j_isucc] at h_nil
                              simp only [nil_takeUntil]
                              exact h_nil
                        constructor
                        · exact hs_path.support_nodup
                        · constructor
                          · exact eady_j_isucc_tail_Nodup
                          · exact Disjoint_s_j_isucc
                      · constructor
                        · simp
                        · simp only [List.disjoint_singleton, mem_support_append_iff, support_copy,
                          not_or, eady_j_isucc]
                          constructor
                          · have la : p.getVert 0 = a := by
                              rw [SimpleGraph.Walk.getVert_zero]
                            have a_in : a ∈ p.support := by simp only [start_mem_support]
                            by_contra ha
                            obtain h' := List.mem_inter_of_mem_of_mem ha a_in
                            rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                            have : p.getVert 0 = p.getVert j := by
                              simpa [la] using h'
                            obtain congr := getVert_congr (h := this) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                            omega
                          · by_contra H
                            have H4 : ¬ a ∈ ((p.takeUntil _ h1).reverse.takeUntil _ h_in_i_succ).support := by
                              by_contra H
                              have h_in : ∃ k, p.getVert k = a ∧ k ≥ i + 1 ∧ k ≤ j := by
                                obtain hx_left := h_indices_trans_3 (hp := hp_path) (hx := H) (i := j) (j := i + 1) (hn := h_in_i_succ) (len := by omega) (hl := by omega)
                                rcases hx_left with ⟨k , hk, hj⟩
                                use j - k
                                refine ⟨hk, by omega, by omega⟩
                              rcases h_in with ⟨k, h1, h2⟩
                              have eq : a = p.getVert 0 := by simp
                              conv at h1 =>
                                right; rw [eq]
                              obtain congr := getVert_congr (h := h1) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                            contradiction
                    · constructor
                      · simp only [support_concat, support_copy, List.concat_eq_append, ne_eq,
                        support_ne_nil, not_false_eq_true, tail_append_of_ne_nil, eady_ab]
                        rw [List.nodup_append']
                        constructor
                        · apply tail_Ispath
                          · apply SimpleGraph.Walk.IsPath.takeUntil
                            exact hp_path
                          · simp only [nil_takeUntil]
                            by_contra h
                            rw [SimpleGraph.Walk.getVert_eq_support_getElem p (by linarith)] at h
                            simp only [mem_univ, get_eq_getElem, true_and] at hiJ
                            rw [← h] at hiJ
                            obtain h' := ore_endpoints_adjacent hG ⟨hp_path, hp_max⟩ (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                            contradiction
                        · constructor
                          · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
                          · simp only [List.disjoint_singleton]
                            exact Disjoint_take_i_b
                      · simp only [support_concat, List.concat_eq_append, support_copy, ne_eq,
                        support_ne_nil, not_false_eq_true, tail_append_of_ne_nil,
                        disjoint_append_right, disjoint_append_left, singleton_disjoint,
                        List.disjoint_singleton, mem_append, mem_support_append_iff, List.mem_cons,
                        not_mem_nil, or_false, not_or, eady_va, eady_ab]
                        constructor
                        · constructor
                          · exact s_append_jisucc_Disjoint
                          · exact not_exist_take_i
                        · constructor
                          · constructor
                            · exact not_exist_s
                            · simp only [support_copy, eady_j_isucc]
                              exact not_exist_b_take_reverse
                          · by_contra h_eq
                            obtain eq_symm := Eq.symm h_eq
                            contradiction
                  · constructor
                    · rw [SimpleGraph.Walk.nil_iff_support_eq] at h_nil
                      simp only [h_nil, List.tail_cons, nodup_nil]
                    · rw [SimpleGraph.Walk.nil_iff_support_eq] at h_nil
                      simp only [h_nil, List.tail_cons, disjoint_nil_right]
                · constructor
                  · obtain H := List.nodup_append' (l₁ := eady_va.support) (l₂ := eady_ab.support.tail)
                    have : (eady_va.append eady_ab).support.Nodup = (eady_va.support ++ eady_ab.support.tail).Nodup  := by
                      rw [Walk.support_append]
                    rw [this, H]
                    constructor
                    · simp only [support_concat, List.concat_eq_append, eady_va]
                      rw [List.nodup_append']
                      constructor
                      · obtain H := List.nodup_append' (l₁ := s.support) (l₂ := eady_j_isucc.support.tail)
                        have : (s.append eady_j_isucc).support.Nodup = (s.support ++ eady_j_isucc.support.tail).Nodup  := by
                          rw [Walk.support_append]
                        rw [this, H]
                        have eady_j_isucc_tail_Nodup : eady_j_isucc.support.tail.Nodup := by
                          rcases Decidable.em (eady_j_isucc.Nil) with h_nil | h_nil
                          · rw [SimpleGraph.Walk.nil_iff_support_eq] at h_nil
                            simp only [h_nil, List.tail_cons, nodup_nil]
                          · simp only [support_copy, eady_j_isucc]
                            apply tail_Ispath
                            · apply SimpleGraph.Walk.IsPath.takeUntil
                              simp only [isPath_reverse_iff]
                              apply SimpleGraph.Walk.IsPath.takeUntil
                              exact hp_path
                            · simp only [nil_copy, nil_takeUntil, eady_j_isucc] at h_nil
                              simp only [nil_takeUntil]
                              exact h_nil
                        constructor
                        · exact hs_path.support_nodup
                        · constructor
                          · exact eady_j_isucc_tail_Nodup
                          · exact Disjoint_s_j_isucc
                      · constructor
                        · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
                        · simp only [List.disjoint_singleton, mem_support_append_iff, support_copy,
                          not_or, eady_j_isucc]
                          constructor
                          · have la : p.getVert 0 = a := by
                              rw [SimpleGraph.Walk.getVert_zero]
                            have a_in : a ∈ p.support := by simp only [start_mem_support]
                            by_contra ha
                            obtain h' := List.mem_inter_of_mem_of_mem ha a_in
                            rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                            have : p.getVert 0 = p.getVert j := by simpa [la] using h'
                            obtain congr := getVert_congr (h := this) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                            rw [← congr] at hji_ne
                            have : i.val = 0 := by omega
                            simp only [mem_univ, this, get_eq_getElem, true_and] at hiJ
                            rw [SimpleGraph.Walk.getVert_eq_support_getElem p (h := by omega)] at la
                            rw [la] at hiJ
                            obtain h' := ore_endpoints_adjacent hG  ⟨hp_path, hp_max⟩  (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                            contradiction
                          · by_contra H
                            have H4 : ¬ a ∈ ((p.takeUntil _ h1).reverse.takeUntil _ h_in_i_succ).support  := by
                              by_contra H
                              have h_in : ∃ k, p.getVert k = a ∧ k ≥ i + 1 ∧ k ≤ j := by
                                obtain hx_left := h_indices_trans_3 (hp := hp_path) (hx := H) (i := j) (j := i + 1) (hn := h_in_i_succ) (len := by omega) (hl := by omega)
                                rcases hx_left with ⟨k , hk, hj⟩
                                use j - k
                                refine ⟨hk, by omega, by omega⟩
                              rcases h_in with ⟨k, h1, h2⟩
                              have eq : a = p.getVert 0 := by simp only [getVert_zero]
                              conv at h1 => right; rw [eq]
                              obtain congr := getVert_congr (h := h1) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                            contradiction
                    · constructor
                      · simp only [support_concat, support_copy, List.concat_eq_append, ne_eq,
                        support_ne_nil, not_false_eq_true, tail_append_of_ne_nil, eady_ab]
                        rw [List.nodup_append']
                        constructor
                        · apply tail_Ispath
                          · apply SimpleGraph.Walk.IsPath.takeUntil
                            exact hp_path
                          · simp only [nil_takeUntil]
                            by_contra h
                            rw [SimpleGraph.Walk.getVert_eq_support_getElem p (by linarith)] at h
                            simp only [mem_univ, get_eq_getElem, true_and] at hiJ
                            rw [← h] at hiJ
                            obtain h' := ore_endpoints_adjacent hG  ⟨hp_path, hp_max⟩ (hv_not_in_p := ⟨v, hv_not_in_p⟩)
                            contradiction
                        · constructor
                          · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
                          · simp only [List.disjoint_singleton]
                            exact Disjoint_take_i_b
                      · simp only [support_concat, List.concat_eq_append, support_copy, ne_eq,
                        support_ne_nil, not_false_eq_true, tail_append_of_ne_nil,
                        disjoint_append_right, disjoint_append_left, singleton_disjoint,
                        List.disjoint_singleton, mem_append, mem_support_append_iff, List.mem_cons,
                        not_mem_nil, or_false, not_or, eady_va, eady_ab]
                        constructor
                        · constructor
                          · exact s_append_jisucc_Disjoint
                          · exact not_exist_take_i
                        · constructor
                          · constructor
                            · exact not_exist_s
                            · simp only [support_copy, eady_j_isucc]
                              exact not_exist_b_take_reverse
                          · by_contra h_eq
                            obtain eq_symm := Eq.symm h_eq
                            contradiction
                  · constructor
                    · simp only [eady_bj_succ]
                      apply tail_Ispath
                      · apply SimpleGraph.Walk.IsPath.takeUntil
                        simp only [isPath_reverse_iff]
                        exact hp_path
                      · simp only [nil_takeUntil, eady_bj_succ] at h_nil
                        simp only [nil_takeUntil]
                        exact h_nil
                    · have append_total_Disjoint : (eady_va.append eady_ab).support.Disjoint eady_bj_succ.support.tail := by
                        rw [← List.inter_eq_nil_iff_disjoint, ← List.toFinset_eq_empty_iff]
                        simp only [toFinset_inter]
                        have h : eady_bj_succ.support.tail ⊆ eady_bj_succ.support := by
                          apply List.tail_subset
                        rw [List.subset_def] at h
                        apply Finset.Subset.antisymm
                        · intro x hx
                          rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                          simp only [mem_toFinset, mem_support_append_iff] at hx_left
                          simp only [mem_toFinset] at hx_right
                          obtain H := h hx_right
                          have h_indices_right : ∃ k, p.getVert k = x ∧ k ≥ (j + 1) ∧ k < p.length := by
                            simp only [eady_bj_succ] at H
                            obtain H := h_indices_trans_1 (hp := hp_path) (hx := H) (i := (j + 1)) (h := h2') (len := by omega)
                            rcases H with ⟨k , hk, hj⟩
                            use (p.length - k)
                            rw [SimpleGraph.Walk.getVert_reverse] at hk
                            refine ⟨hk, by omega, ?_⟩
                            simp only [tsub_lt_self_iff]
                            refine ⟨by omega, ?_⟩
                            by_contra h
                            have l : k = 0 := by omega
                            rw [l] at hk
                            simp only [tsub_zero, getVert_length] at hk
                            rw [← hk] at hx_right
                            have not_nil : ¬ eady_bj_succ.Nil := by
                              simp_all only [ge_iff_le, ne_eq, length_support,
                                add_tsub_cancel_right, support_reverse, mem_reverse, not_le,
                                gt_iff_lt, getVert_mem_support, implies_true, eq_iff_iff, mem_inter,
                                mem_toFinset, mem_support_append_iff, true_and, zero_le,
                                lt_self_iff_false, not_false_eq_true]
                            have h' : eady_bj_succ.IsPath := by
                              simp only [eady_bj_succ]
                              apply SimpleGraph.Walk.IsPath.takeUntil
                              simp only [isPath_reverse_iff]
                              exact hp_path
                            obtain not_in := end_not_exsit_tail (p := eady_bj_succ) (h := not_nil) (hp := h')
                            contradiction
                          rcases h_indices_right with ⟨k₁, hk₁_eq, hk₁_ge⟩
                          rcases hx_left with (hx_left | hx_left)
                          · simp only [support_concat, List.concat_eq_append, mem_append,
                            mem_support_append_iff, List.mem_cons, not_mem_nil, or_false,
                            eady_va] at hx_left
                            rcases hx_left with ((hs | he) | ha)
                            · have h2 : x ∈ p.support := by
                                rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
                                use k₁
                                refine ⟨hk₁_eq, by omega⟩
                              have h3 : x = p.getVert j := by
                                have h_inter : x ∈ s.support ∩ p.support := by
                                  simp only [mem_inter_iff]
                                  refine ⟨hs, h2⟩
                                rw [hs_inter, List.singleton_eq] at h_inter
                                simp_all only [mem_inter, mem_toFinset, List.mem_cons, not_mem_nil, or_false]
                              rw [h3] at hk₁_eq
                              obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                            · simp only [support_copy, eady_j_isucc] at he
                              have h_indices_left : ∃ k, p.getVert k = x ∧ k ≥ i + 1 ∧ k ≤ j := by
                                obtain H := h_indices_trans_3 (hp := hp_path) (hx := he) (i := j) (j := i + 1) (hn := h_in_i_succ) (len := by omega) (hl := by omega)
                                rcases H with ⟨k , hk, hj⟩
                                use j - k
                                refine ⟨hk, ?_, by simp⟩
                                omega
                              rcases h_indices_left with ⟨k₂, hk₂_eq, hk₂_ge⟩
                              rw [← hk₂_eq] at hk₁_eq
                              obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                            · have eq : p.getVert 0 = a := by simp
                              rw [← eq] at ha
                              rw [ha] at hk₁_eq
                              obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                          · simp only [support_concat, support_copy, List.concat_eq_append,
                            mem_append, List.mem_cons, not_mem_nil, or_false, eady_ab] at hx_left
                            rcases hx_left with (hx_left | hx_left)
                            · have h_indices_left : ∃ k, p.getVert k = x ∧ k ≤ i := by
                                obtain H := h_indices_trans_2 (hp := hp_path) (hx := hx_left) (i := i) (h := h3) (len := by omega)
                                exact H
                              rcases h_indices_left with ⟨k₂, hk₂_eq, hk₂_ge⟩
                              rw [← hk₂_eq] at hk₁_eq
                              obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                            · have eq : p.getVert p.length = b := by simp
                              rw [← eq] at hx_left
                              rw [hx_left] at hk₁_eq
                              obtain congr := getVert_congr (h := hk₁_eq) (hp := hp_path) (hn1 := by omega) (hn2 := by omega)
                              omega
                        · apply Finset.empty_subset
                      exact append_total_Disjoint
              have hq_length : q.length = p.length + s.length := by
                simp only [Walk.length_append, Walk.length_concat, length_copy, q, eady_va,
                  eady_j_isucc, eady_ab, eady_bj_succ]
                have len_take_i : (p.takeUntil (p.getVert i) h_in_i).length = i := by
                  rw [len_takeUntil (hp := hp_path)]
                  linarith
                rw [len_take_i]
                have : p.reverse.getVert (p.reverse.takeUntil _ h2').length = p.reverse.getVert (p.length - (j + 1)) := by
                  rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
                  rw [Nat.sub_sub_self]
                  have l': i + 1 < p.support.length := by
                    omega
                  simp only [length_support, add_lt_add_iff_right] at l'
                  linarith
                have hp_reverse_path : p.reverse.IsPath := by
                  simp only [isPath_reverse_iff]
                  exact hp_path
                obtain congr := getVert_congr (h := this) (hp := hp_reverse_path) (hn1 := by apply SimpleGraph.Walk.length_takeUntil_le) (hn2 := by simp only [Walk.length_reverse,
                  tsub_le_iff_right, le_add_iff_nonneg_right, zero_le])
                rw [congr]
                rcases Decidable.em (j = i) with hlen | hlen
                · have :  p.getVert (j + 1) ∈ (p.takeUntil (p.getVert j) h1).support := by
                    have eq : p.getVert (j + 1) = p.getVert (i + 1) := by
                      rw [hlen]
                    simpa [eq] using h_in_i_succ
                  have : ¬ p.getVert (j + 1) ∈ (p.takeUntil _ h1).support := by
                    apply next_not_exsit_takeUntil
                    · exact hp_path
                    · simp_all only [ge_iff_le, ne_eq, length_support, add_tsub_cancel_right,
                      get_eq_getElem, true_and, mem_univ, support_reverse, mem_reverse,
                      add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, not_false_eq_true,
                      gt_iff_lt, lt_add_iff_pos_right, _root_.zero_lt_one, getVert_mem_support,
                      not_true_eq_false]
                  contradiction
                · have len : ((p.takeUntil _ h1).reverse.takeUntil _ h_in_i_succ).length = j - (i + 1) := by
                    rw [len_takeUntil_reverse_takeUntil (hp := hp_path)]
                    · linarith
                    · omega
                  rw [len, ← Nat.add_sub_assoc, ← Nat.add_sub_assoc, Nat.add_right_comm (m := 1), Nat.sub_add_cancel, Nat.add_assoc (m := j), Nat.sub_add_comm, Nat.add_sub_cancel]
                  · linarith
                  · simp only [le_add_iff_nonneg_left, zero_le]
                  · omega
                  · omega
                  · omega
              have : q.length > p.length := by
                rw [hq_length]
                have : 0 < s.length := by
                  rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
                  by_contra! H
                  obtain l := SimpleGraph.Walk.Nil.eq H
                  simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
                linarith
              obtain h := h hq_path
              linarith [hq_length , this]
          · have hJ : p.length ≤ j := by linarith
            obtain eq := SimpleGraph.Walk.getVert_of_length_le p hJ
            let s' : G.Walk v b := s.copy rfl eq
            have s'_path : s'.IsPath := by
              unfold s'
              simp only [isPath_copy]
              exact hs_path
            let q  : G.Walk a v := p.append s'.reverse
            have hq_path : q.IsPath := by
              unfold q
              simp_all only [ge_iff_le, ne_eq]
              rw [SimpleGraph.Walk.isPath_def]
              obtain H := List.nodup_append'  (l₁ :=  p.support) (l₂ := s'.reverse.support.tail)
              have :  (p.append s'.reverse).support = (p.support ++ (s'.reverse).support.tail) := by
                rw [Walk.support_append]
              rw [this, H]
              constructor
              · exact hp_path.support_nodup
              · constructor
                · rw [← SimpleGraph.Walk.support_tail_of_not_nil]
                  · rw [← SimpleGraph.Walk.isPath_def]
                    apply SimpleGraph.Walk.IsPath.tail
                    apply SimpleGraph.Walk.IsPath.reverse
                    exact s'_path
                  · intro H
                    rw [SimpleGraph.Walk.nil_reverse] at H
                    obtain H' := SimpleGraph.Walk.Nil.eq H
                    simp_all only [not_true_eq_false]
                · have H3 : p.support.Disjoint s'.reverse.support.tail := by
                    rw [← List.inter_eq_nil_iff_disjoint, ← List.toFinset_eq_empty_iff]
                    simp only [support_reverse, tail_reverse, inter_reverse, toFinset_inter]
                    apply Finset.Subset.antisymm
                    · intro x hx
                      rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                      simp only [mem_toFinset] at hx_left
                      simp only [mem_toFinset] at hx_right
                      have h_indices_left : x ∈ p.support := by omega
                      have h_indices_right : ¬ x ∈ p.support := by
                        by_contra H
                        obtain h := List.mem_of_mem_dropLast hx_right
                        obtain h' := List.mem_inter_of_mem_of_mem h h_indices_left
                        obtain h_copy := SimpleGraph.Walk.support_copy s rfl eq
                        rw [← h_copy] at hs_inter
                        rw [hs_inter,  List.singleton_eq, List.mem_singleton] at h'
                        have h'' : s'.support ≠ [] := by
                          simp_all only [not_le, gt_iff_lt, not_lt, support_reverse, tail_reverse,
                            nodup_reverse, disjoint_reverse_right, mem_inter, mem_toFinset,
                            end_mem_support, true_and, support_copy, ne_eq, support_ne_nil,
                            not_false_eq_true]
                        have s_eq : (s'.support.dropLast ++ [p.getVert (j)]).reverse= s'.support.reverse := by
                          rw [← List.dropLast_append_getLast (l := s'.support)]
                          · simp only [getLast_support, ne_eq, cons_ne_self, not_false_eq_true,
                            dropLast_append_of_ne_nil, dropLast_singleton, List.append_nil]
                            rw [eq]
                          · exact h''
                        rw [List.reverse_concat'] at s_eq
                        have l : (s'.support.reverse).Nodup := by
                          simp only [nodup_reverse]
                          exact s'_path.support_nodup
                        rw [← s_eq] at l
                        obtain  H:= List.Nodup.notMem  l
                        have : x ∉ s'.support.dropLast.reverse := by
                          rw [← eq] at h'
                          rw [h']
                          exact H
                        simp only [mem_reverse] at this
                        contradiction
                      contradiction
                    · apply Finset.empty_subset
                  exact H3
            have hq_length : q.length = p.length + s'.length := by
              simp only [Walk.length_append, Walk.length_reverse, q]
            have len_le : q.length > p.length := by
              rw [hq_length]
              have : 0 < s'.length:= by
                rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
                intro H
                obtain H' := SimpleGraph.Walk.Nil.eq H
                simp_all only [ge_iff_le, ne_eq, end_mem_support, not_true_eq_false]
              omega
            have := hp_max a v q hq_path
            linarith [hq_length, this]
      have card_I : I.card = G.degree a := by
        unfold I
        rw [← SimpleGraph.card_neighborSet_eq_degree G a]
        simp only [List.get_eq_getElem]
        apply Finset.card_eq_of_equiv_fintype
        have h1 : ({i | G.Adj a (p.support.get ⟨(i + 1) , by omega⟩)} :
          Finset (Fin (p.support.length - 1 ))) = I := by
          ext i
          simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and, I]
        have h2 : ({x | x ∈ {x | G.Adj a x}} )= (G.neighborSet a).toFinset := by
          ext v
          simp only [Set.mem_setOf_eq, Set.coe_toFinset, mem_neighborSet]
        simp only [List.get_eq_getElem, Set.mem_setOf_eq, Set.coe_toFinset] at h1 h2
        simp_all only [ne_eq, ge_iff_le]
        let f : I → G.neighborSet a := fun ⟨i, hi⟩ => ⟨p.support.get ⟨i.val + 1 , by omega⟩, by
          simp only [List.get_eq_getElem, mem_neighborSet] at hi ⊢
          rw [← h1] at hi
          simp only [Finset.mem_filter, mem_univ, true_and] at hi
          exact hi⟩
        have hinj : Function.Injective f := by
          intro x y h
          simp only [List.get_eq_getElem, Subtype.mk.injEq, f] at h ⊢
          ext
          have idx_x : p.support.idxOf (p.support.get ⟨x.val + 1, by omega⟩) = x.val + 1:= by
            apply List.Nodup.idxOf_getElem
            exact hp_path.support_nodup
          have idx_y : p.support.idxOf (p.support.get ⟨y.val + 1 , by omega⟩) = y.val + 1:= by
            apply List.Nodup.idxOf_getElem
            simp_all only [get_eq_getElem]
            exact hp_path.support_nodup
          simp_all only [get_eq_getElem, Nat.add_right_cancel_iff]
        have hsurj : Function.Surjective f := by
          intro ⟨v, hv⟩
          simp only [G.mem_neighborSet] at hv
          have : ∃ (i : Fin (p.support.length - 1)), p.support.get ⟨i.val + 1, by omega⟩ = v := by
            let k := p.support.idxOf v
            have hv_mem : v ∈ p.support := by
              by_contra H
              have hav : G.Adj a v := by omega
              let q : G.Walk v b := (cons hav.symm .nil).append p
              have hq_path : q.IsPath := by
                unfold q
                simp_all only [mem_neighborSet, Walk.cons_append, Walk.nil_append,
                  cons_isPath_iff, not_false_eq_true, and_self]
              have hq_length : q.length = p.length + 1 := by simp only [Walk.cons_append,
                Walk.nil_append, Walk.length_cons, q]
              have := hp_max v b q ⟨hq_path.1, ?_⟩
              · rw [hq_length] at this
                linarith
              · rw [SimpleGraph.Walk.isPath_def] at hq_path
                omega
            have hk_lt : k < p.support.length := by
              apply List.idxOf_lt_length_iff.mpr
              exact hv_mem
            have hk_pos : 0 < k := by
              by_contra! H
              have l : k = 0 := by omega
              have : p.getVert 0 = a := by simp only [getVert_zero]
              have : p.getVert k = v := by
                have l : k ≤ p.length := by omega
                rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                simp only [getElem_idxOf, k]
              simp_all only [mem_neighborSet, length_support, lt_add_iff_pos_left,
                Order.lt_add_one_iff, zero_le, le_refl, getVert_zero, SimpleGraph.irrefl]
            have : k - 1 < (p.support.length - 1)  := by omega
            let i : Fin (p.support.length - 1 ) := ⟨k - 1, this⟩
            refine ⟨i, ?_⟩
            calc
            p.support.get ⟨i.val + 1 , by omega⟩ = p.support.get ⟨k , by omega⟩ := by
              simp_all only [mem_neighborSet, get_eq_getElem]
              have : k - 1 + 1 = k := by omega
              simp only [this, i]
            _ = p.support.get ⟨k , by omega⟩ := by
              simp_all only [mem_neighborSet, get_eq_getElem]
            _ = v := by
              obtain h := List.get_idxOf hp_path.support_nodup
              simp_all only [mem_neighborSet, get_eq_getElem]
              simp only [getElem_idxOf, k]
          rcases this with ⟨i, hi⟩
          have mem : i ∈ I := by
            unfold I
            simp only [List.get_eq_getElem]
            simp only [Finset.mem_filter, mem_univ, true_and]
            simp only [get_eq_getElem] at hi
            rw [hi]
            exact hv
          refine ⟨⟨i, mem⟩, ?_⟩
          simp only [List.get_eq_getElem, Subtype.mk.injEq, f]
          simp_all only [mem_neighborSet, get_eq_getElem]
        obtain h := Equiv.ofBijective f ⟨hinj, hsurj⟩
        exact Equiv.ofBijective f ⟨hinj, hsurj⟩
      have card_J : J.card = G.degree b := by
        unfold J
        rw [← SimpleGraph.card_neighborSet_eq_degree G b]
        simp only [List.get_eq_getElem]
        apply Finset.card_eq_of_equiv_fintype
        have h1 : ({i | G.Adj (p.support.get ⟨i , by omega⟩) b} :
          Finset (Fin (p.support.length - 1))) = J := by
          ext i
          simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and, J]
        have h2 : ({x | x ∈ {x | G.Adj x b}} )= (G.neighborSet b).toFinset := by
          ext v
          simp only [Set.mem_setOf_eq, Set.coe_toFinset, mem_neighborSet]
          rw [SimpleGraph.adj_comm]
        simp only [List.get_eq_getElem, Set.mem_setOf_eq, Set.coe_toFinset] at h1 h2
        simp_all only [ne_eq, ge_iff_le]
        let f : J → G.neighborSet b := fun ⟨i, hi⟩ =>
          ⟨p.support.get ⟨i.val , by omega⟩, by
            simp only [List.get_eq_getElem, mem_neighborSet] at hi ⊢
            rw [← h1] at hi
            simp only [Finset.mem_filter, mem_univ, true_and] at hi
            rw [SimpleGraph.adj_comm]
            exact hi⟩
        have hinj : Function.Injective f := by
          intro x y h
          simp only [List.get_eq_getElem, Subtype.mk.injEq, f] at h ⊢
          ext
          have idx_x : p.support.idxOf (p.support.get ⟨x.val , by omega⟩) = x.val := by
            apply List.Nodup.idxOf_getElem
            exact hp_path.support_nodup
          have idx_y : p.support.idxOf (p.support.get ⟨y.val, by omega⟩) = y.val := by
            apply List.Nodup.idxOf_getElem
            simp_all only [get_eq_getElem]
            exact hp_path.support_nodup
          simp_all only [get_eq_getElem]
        have hsurj : Function.Surjective f := by
          intro ⟨v, hv⟩
          simp only [G.mem_neighborSet] at hv
          have : ∃ (i : Fin (p.support.length - 1)), p.support.get ⟨i.val, by omega⟩ = v := by
            let k := p.support.idxOf v
            have hv_mem : v ∈ p.support := by
              by_contra H
              have hav : G.Adj b v := by omega
              let q := p.append (Walk.cons hav .nil)
              have hq_path : q.IsPath := by
                unfold q
                obtain H := List.nodup_append'  (l₁ := p.support) (l₂ := (Walk.cons hav nil).support.tail)
                have : (p.append (Walk.cons hav nil)).support.Nodup =
                  (p.support ++ ((Walk.cons hav nil)).support.tail).Nodup  := by
                  rw [Walk.support_append]
                rw [SimpleGraph.Walk.isPath_def]
                rw [this, H]
                simp only [support_cons, support_nil, List.tail_cons, nodup_cons, not_mem_nil,
                  not_false_eq_true, nodup_nil, and_self, List.disjoint_singleton, true_and]
                refine ⟨ hp_path.support_nodup, by omega⟩
              have hq_length : q.length = p.length + 1 := by simp only [Walk.length_append,
                Walk.length_cons, Walk.length_nil, zero_add, q]
              have := hp_max a v q ⟨hq_path.1, ?_⟩
              · rw [hq_length] at this
                linarith
              · rw [SimpleGraph.Walk.isPath_def] at hq_path
                omega
            have hk_lt : k < p.support.length := by
              apply List.idxOf_lt_length_iff.mpr
              exact hv_mem
            have : k < (p.support.length - 1)  := by
              obtain h := Nat.le_sub_one_of_lt hk_lt
              have : k < (p.support.length - 1) ∨ k = p.support.length - 1 := by omega
              rcases this with hlt | heq
              · exact hlt
              · simp_all only [mem_neighborSet, length_support, add_tsub_cancel_right,
                lt_add_iff_pos_right, _root_.zero_lt_one, le_refl, lt_self_iff_false]
                have l1 : p.support.get ⟨p.support.length - 1, by simp⟩ = b := by
                  have h_x_eq : p.getVert (p.support.length - 1) = b := by
                    rw [SimpleGraph.Walk.IsPath.getVert_eq_end_iff]
                    · simp only [length_support, add_tsub_cancel_right]
                    · omega
                    · simp only [length_support, add_tsub_cancel_right, le_refl]
                  have vertex0_is_a : p.support.get ⟨(p.support.length - 1), by simp⟩ = b := by
                    simp
                    rw [Walk.getVert_eq_getD_support] at h_x_eq
                    simp only [length_support, add_tsub_cancel_right, getD_eq_getElem?_getD,
                      lt_add_iff_pos_right, _root_.zero_lt_one, getElem?_pos,
                      Option.getD_some] at h_x_eq
                    omega
                  omega
                have l2: p.support.get ⟨p.support.length - 1, by simp⟩ = v := by
                  conv_lhs => enter [2, 1]; rw [length_support, ← heq]
                  simp only [add_tsub_cancel_right, get_eq_getElem, getElem_idxOf, k]
                simp_all only [length_support, add_tsub_cancel_right, get_eq_getElem,
                  SimpleGraph.irrefl]
            let i : Fin (p.support.length - 1) := ⟨k , this⟩
            refine ⟨i, ?_⟩
            calc
            p.support.get ⟨i.val  , by omega⟩ = p.support.get ⟨k , by omega⟩ := by
              simp_all only [mem_neighborSet, get_eq_getElem]
              simp only [i]
            _ = p.support.get ⟨k , by omega⟩ := by
              simp_all only [mem_neighborSet, get_eq_getElem]
            _ = v := by
              obtain h := List.get_idxOf hp_path.support_nodup
              simp_all only [mem_neighborSet, get_eq_getElem]
              simp only [getElem_idxOf, k]
          rcases this with ⟨i, hi⟩
          have mem : i ∈ J := by
            unfold J
            simp only [List.get_eq_getElem]
            simp only [Finset.mem_filter, mem_univ, true_and]
            simp only [get_eq_getElem] at hi
            rw [hi]
            exact hv.symm
          refine ⟨⟨i, mem⟩, ?_⟩
          simp only [List.get_eq_getElem, Subtype.mk.injEq, f]
          simp_all only [mem_neighborSet, get_eq_getElem]
        exact Equiv.ofBijective f ⟨hinj, hsurj⟩
      have h_union_bound : I.card + J.card ≤ p.length := by
        have : p.support.length = p.length + 1 := by simp
        calc
          I.card + J.card = (I ∪ J).card := by
            obtain h := Finset.card_union_eq_card_add_card (s := I) (t := J)
            have disj : Disjoint I J := by
              rw [disjoint_iff_inter_eq_empty]
              omega
            rw [← h] at disj
            omega
          _ ≤ p.support.length - 1 := by
            simp only [length_support, add_tsub_cancel_right]
            have h_subset : I ∪ J ⊆ Finset.univ := by simp
            have h_union_bound : (I ∪ J).card ≤ p.length := by
              have : p.support.length = p.length + 1 := by simp
              calc
                (I ∪ J).card ≤ p.support.length - 1 := by
                  obtain h := Finset.card_le_univ (s := I ∪ J)
                  simp only [length_support, add_tsub_cancel_right, Fintype.card_fin] at h
                  simp only [length_support, add_tsub_cancel_right]
                  exact h
                _ = p.length := by
                  rw [this]
                  omega
            exact h_union_bound
          _ = p.length := by
            simp
      rw [card_I, card_J] at h_union_bound
      have : G.degree a + G.degree b ≤ p.length := by omega
      have sum_card : I.card + J.card = G.degree a + G.degree b := by
        rw [card_I, card_J]
      have h_union_card : (I ∪ J).card = I.card + J.card := by
        rw [Finset.card_union]
        have disj : Disjoint I J := by
          rw [disjoint_iff_inter_eq_empty]
          omega
        rw [disjoint]
        simp
      rw [card_I, card_J] at h_union_card
      have h_total_lower_bound : Fintype.card V ≥ p.length + 1 := by
        obtain h := SimpleGraph.Walk.IsPath.length_lt hp_path
        linarith
      have h_degree_lower_bound : G.degree a + G.degree b ≥ p.length + 1 := by
        obtain no_adj := ore_endpoints_adjacent hG (hp := ⟨hp_path, hp_max⟩) (hv_not_in_p := ⟨v, hv_not_in_p⟩)
        obtain h := h_ore a b h_neq no_adj
        linarith
      have : p.length < G.degree a + G.degree b := by linarith
      linarith








lemma Walk.edge_get_verts {G : SimpleGraph V} {u w : V} (p : G.Walk u w) (hp : p.IsPath) :
    ∀ (i :ℕ) (hi : i < p.edges.length), p.edges.get ⟨i, hi⟩ = s(p.getVert i, p.getVert (i + 1)) := by
  induction p with
  | nil =>
    intro i hi
    simp only [edges_nil, List.length_nil, not_lt_zero] at hi
  | cons hd tl ih =>
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        simp_all
      · rcases Decidable.em (i = tl.length) with H
        rcases H with (hA | hB)
        · conv_lhs => enter [2, 1];rw [show i = i - 1 + 1 by rw [Nat.sub_add_cancel (by omega)]]
          conv_rhs => enter [1, 1];rw [show i = i - 1 + 1 by rw [Nat.sub_add_cancel (by omega)]]
          rw [← List.get_tail]
          · simp_all only [length_edges, get_eq_getElem, cons_isPath_iff, edges_cons,
            List.length_cons, lt_add_iff_pos_right, _root_.zero_lt_one, List.tail_cons,
            getVert_cons_succ, getVert_length, forall_const, implies_true]
            have : tl.length = tl.support.length - 1 := by
              rw [SimpleGraph.Walk.length_support]; simp
            have l2 : tl.length - 1 < tl.edges.length := by
              rw [SimpleGraph.Walk.length_edges]; omega
            obtain  H := ih (hp := hp.1) (i := tl.length - 1) l2
            simp only [get_eq_getElem] at H
            rw [H, Nat.sub_add_cancel (by omega)]
            simp only [getVert_length]
          · simp_all only [length_edges, get_eq_getElem, cons_isPath_iff, edges_cons,
            List.length_cons, lt_add_iff_pos_right, _root_.zero_lt_one, List.tail_cons,
            tsub_lt_self_iff, and_true, forall_const, implies_true]
            omega
        · conv_lhs => enter [2, 1];rw [show i = i - 1 + 1 by rw [Nat.sub_add_cancel (by omega)]]
          rw [← List.get_tail]
          · have : 0 < i := Nat.pos_of_ne_zero hi0
            have : (Walk.cons hd tl).getVert i = tl.getVert (i - 1) := by
              rw [show i = i -1 + 1  by omega]
              simp only [getVert, add_tsub_cancel_right]
            have : (Walk.cons hd tl).getVert (i + 1) = tl.getVert i := by
              simp only [getVert]
            simp_all only [length_edges, get_eq_getElem, cons_isPath_iff, edges_cons,
              List.length_cons, getVert_cons_succ, List.tail_cons, forall_const, implies_true]
            have hi' : i < tl.edges.length := by
              have := Nat.sub_lt (by omega) (by omega)
              simp_all only [length_edges, get_eq_getElem, forall_const, cons_isPath_iff,
                not_false_eq_true, and_self, edges_cons, List.length_cons, tsub_self, gt_iff_lt]
              have hi' : i < tl.length ∨ i = tl.length := by omega
              rcases hi' with (hA | hB)
              · omega
              · simp_all
            have l : i - 1 < tl.edges.length := by omega
            obtain H' := ih (hp := hp.1) (i := i - 1) l
            rw [Nat.sub_add_cancel] at H'
            · rw [← H']
              simp only [get_eq_getElem]
            · omega
          simp_all only [length_edges, get_eq_getElem, cons_isPath_iff, edges_cons,
            List.length_cons, List.tail_cons, forall_const, implies_true]
          omega



lemma getVert_length_dropUntil {G : SimpleGraph V} {u v w : V} [DecidableEq V] {p : G.Walk v w} (h : u ∈ p.support) :
    p.reverse.getVert (p.dropUntil _ h).length = u := by
  rw [SimpleGraph.Walk.getVert_reverse]
  have := congr_arg₂ (y := p.length - (p.dropUntil _ h).length) getVert (p.take_spec h) rfl
  have len : p.length = (p.dropUntil u h).length + (p.takeUntil u h).length := by
    rw [add_comm]
    rw [← SimpleGraph.Walk.length_edges, ← SimpleGraph.Walk.length_edges,
      ← SimpleGraph.Walk.length_edges]
    rw [ ← List.length_append]
    conv_rhs => enter [1]; rw [← SimpleGraph.Walk.edges_append (p := p.takeUntil u h), SimpleGraph.Walk.take_spec]
  rw [getVert_append] at this
  split at this
  · omega
  · rw [← this, Nat.sub_sub, ← len]; simp






/--
Under the Ore condition, a Hamiltonian path must exist in the graph.
-/
lemma maximal_hamiltonian {G : SimpleGraph V} [Fintype V] [DecidableEq V] [G.LocallyFinite] {hG : G.Connected} {a b : V} (p : G.Walk a b) (hp : Walk.IsMaxlongPath p) {h_order : Fintype.card V ≥ 3} {h_ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ Fintype.card V} :
    p.IsHamiltonian := by
  classical
  obtain H := maximal_path_extends_or_hamiltonian
    (hG := hG) (p := p) (hp := hp) (h_order := h_order) (h_ore := h_ore)
  apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
  · unfold Walk.IsMaxlongPath at hp
    exact hp.1
  · apply H




lemma ore_adjacent {G : SimpleGraph V} (hG : G.Connected) [G.LocallyFinite] [Fintype V] (h_ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ Fintype.card V) {h_order : Fintype.card V ≥ 3} {a b : V} {h_ne : a ≠ b} {p : G.Walk a b} {hp : Walk.IsMaxlongPath p} {h_ab : ¬ G.Adj a b}:
  ∃ (k : (Fin (Fintype.card V - 1))), G.Adj a (p.getVert (k.val + 1)) ∧ G.Adj  (p.getVert k.val) b := by
  have h_all : ∀ v : V, v ∈ p.support := by
    intro v
    unfold Walk.IsMaxlongPath at hp
    obtain H := maximal_path_extends_or_hamiltonian (hG := hG) (hp := hp) (h_order := h_order) (h_ore := h_ore)
    simp_all only [ne_eq, ge_iff_le]
  have h_vertices_length : p.support.length = Fintype.card V := by
    rw [SimpleGraph.Walk.length_support]
    classical
    rw [SimpleGraph.Walk.IsHamiltonian.length_eq]
    · rw [Nat.sub_add_cancel]
      omega
    · apply maximal_hamiltonian (hG := hG) (hp := hp) (h_order := h_order) (h_ore := h_ore)
  classical
  let F : V → Fin (Fintype.card V ) := fun v =>
    ⟨p.support.idxOf v, by
    have h_mem : v ∈ p.support := h_all v
    have h_length : p.support.length = Fintype.card V := by
      exact h_vertices_length
    rw [← h_length]
    apply List.idxOf_lt_length_iff.mpr
    exact h_mem⟩
  let I : Finset (Fin (Fintype.card V - 1)) :=
    (Finset.univ : Finset (Fin (Fintype.card V - 1))).filter fun i =>
      G.Adj a (p.support.get ⟨i.val + 1, by
        have : p.support.length = Fintype.card V := by omega
        have : i.val + 1 ≤   Fintype.card V  := by omega
        omega⟩)
  let J : Finset (Fin (Fintype.card V - 1)) :=
    (Finset.univ : Finset (Fin (Fintype.card V - 1))).filter fun i =>
      G.Adj (p.support.get ⟨i.val  , by
        have : i.val < p.support.length := by omega
        omega⟩) b
  have h_card_I : I.card = G.degree a := by
    unfold I
    rw [← SimpleGraph.card_neighborSet_eq_degree G a]
    apply Finset.card_eq_of_equiv_fintype
    have h1 : ({i | G.Adj a ( p.support.get ⟨i + 1, by rw [h_vertices_length]; omega⟩)} :
      Finset (Fin (Fintype.card V - 1))) = I := by
      ext i
      simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and, I]
    have h2 : ({x | x ∈ {x | G.Adj a x}} )= (G.neighborSet a).toFinset := by
      ext v
      simp
    simp only [List.get_eq_getElem, Set.mem_setOf_eq, Set.coe_toFinset] at h1 h2
    simp_all only [ne_eq, ge_iff_le]
    let f  : I → G.neighborSet a := fun ⟨i, hi⟩ =>
      ⟨ p.support.get ⟨i.val + 1, by omega⟩, by
        simp only [List.get_eq_getElem, mem_neighborSet] at hi ⊢
        rw [← h1] at hi
        simp only [Finset.mem_filter, mem_univ, true_and] at hi
        exact hi⟩
    have hinj : Function.Injective f := by
      intro x y h
      simp only [List.get_eq_getElem, Subtype.mk.injEq, f] at h ⊢
      ext
      have idx_x :  p.support.idxOf ( p.support.get ⟨x.val + 1, by omega⟩) = x.val + 1:= by
        apply List.Nodup.idxOf_getElem
        unfold Walk.IsMaxlongPath at hp
        exact hp.1.support_nodup
      have idx_y :  p.support.idxOf ( p.support.get ⟨y.val + 1, by omega⟩) = y.val + 1:= by
        apply List.Nodup.idxOf_getElem
        unfold Walk.IsMaxlongPath at hp
        exact hp.1.support_nodup
      simp_all only [get_eq_getElem, Nat.add_right_cancel_iff]
    have hsurj : Function.Surjective f := by
      intro ⟨v, hv⟩
      simp only [G.mem_neighborSet] at hv
      have : ∃ (i : Fin (Fintype.card V - 1)), p.support.get ⟨i.val + 1, by omega⟩ = v := by
          let k := p.support.idxOf v
          have hv_mem : v ∈ p.support := h_all v
          have hk_lt : k < p.support.length := by
            apply List.idxOf_lt_length_iff.mpr
            exact hv_mem
          have hk_pos : 0 < k := by
            by_contra! H
            have l : k = 0 := by omega
            have : p.getVert 0 = a := by simp only [getVert_zero]
            have : p.getVert k = v := by
              have l : k ≤ p.length := by omega
              rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
              simp only [getElem_idxOf, k]
            simp_all only [mem_neighborSet, le_refl, getVert_zero, SimpleGraph.irrefl]
          have : k- 1 < Fintype.card V-1  := by omega
          let i : Fin (Fintype.card V -1) := ⟨k - 1, this⟩
          refine ⟨i, ?_⟩
          calc
          p.support.get ⟨i.val + 1, by omega⟩ = p.support.get ⟨k , by omega⟩ := by
            simp_all only [mem_neighborSet, get_eq_getElem]
            have : k - 1 + 1 = k := by omega
            simp only [this, i]
          _ = p.support.get ⟨k, by omega⟩ := by
            simp_all only [mem_neighborSet, get_eq_getElem]
          _ = v := by
            unfold Walk.IsMaxlongPath at hp
            obtain h := List.get_idxOf hp.1.support_nodup
            simp_all only [mem_neighborSet, get_eq_getElem]
            simp only [getElem_idxOf, k]
      rcases this with ⟨i, hi⟩
      have mem : i ∈ I := by
        unfold I
        simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and]
        simp only [get_eq_getElem] at hi
        rw [hi]
        omega
      refine ⟨⟨i, mem⟩, ?_⟩
      simp_all only [List.get_eq_getElem, f, get_eq_getElem]
    obtain h := Equiv.ofBijective f ⟨hinj, hsurj⟩
    exact Equiv.ofBijective f ⟨hinj, hsurj⟩
  have h_card_J : J.card = G.degree b := by
    unfold J
    rw [← SimpleGraph.card_neighborSet_eq_degree G b]
    apply Finset.card_eq_of_equiv_fintype
    have h1 : ({i | G.Adj (p.support.get ⟨i, by rw [h_vertices_length]; omega⟩) b} :
      Finset (Fin (Fintype.card V - 1) ) ) = J := by
      ext i
      simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and, J]
    have h2 : ({x | x ∈ {x | G.Adj x b}} )= (G.neighborSet b).toFinset := by
      ext v
      simp only [Set.mem_setOf_eq, Set.coe_toFinset, mem_neighborSet]
      rw [SimpleGraph.adj_comm]
    simp only [List.get_eq_getElem, Set.mem_setOf_eq, Set.coe_toFinset] at h1 h2
    simp_all only [ne_eq, ge_iff_le, get_eq_getElem]
    let f : J → G.neighborSet b := fun ⟨i, hi⟩ =>
      ⟨p.support.get ⟨i.val , by omega⟩, by
        simp only [List.get_eq_getElem, mem_neighborSet] at hi ⊢
        rw [← h1] at hi
        simp only [Finset.mem_filter, mem_univ, true_and] at hi
        rw [SimpleGraph.adj_comm]
        exact hi⟩
    have hinj : Function.Injective f := by
      intro x y h
      simp only [List.get_eq_getElem, Subtype.mk.injEq, f] at h ⊢
      ext
      have idx_x : p.support.idxOf (p.support.get ⟨x.val , by omega⟩) = x.val := by
        apply List.Nodup.idxOf_getElem
        unfold Walk.IsMaxlongPath at hp
        exact hp.1.support_nodup
      have idx_y : p.support.idxOf (p.support.get ⟨y.val, by omega⟩) = y.val := by
        apply List.Nodup.idxOf_getElem
        unfold Walk.IsMaxlongPath at hp
        exact hp.1.support_nodup
      simp_all only [get_eq_getElem]
    have hsurj : Function.Surjective f := by
      intro ⟨v, hv⟩
      simp only [G.mem_neighborSet] at hv
      have : ∃ (i : Fin (Fintype.card V - 1)), p.support.get ⟨i.val, by omega⟩ = v := by
        let k := p.support.idxOf v
        have hv_mem : v ∈ p.support:= h_all v
        have hk_lt : k < p.support.length := by
          rw [← List.idxOf_lt_length_iff] at hv_mem
          simp only [length_support, k]
          rw [← SimpleGraph.Walk.length_support]
          exact hv_mem
        have h_length : p.support.length = Fintype.card V := by
          simp_all only [mem_neighborSet]
        have hk_pos : 0 < k := by
          by_contra! H
          have l : k = 0 := by omega
          have : p.getVert 0 = a := by simp only [getVert_zero]
          have : p.getVert k = v := by
            have l : k ≤ p.length := by omega
            rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
            simp only [getElem_idxOf, k]
          have : ¬G.Adj b a := by rwa [G.adj_comm] at h_ab
          simp_all only [mem_neighborSet, le_refl, getVert_zero]
        have : k < Fintype.card V - 1 := by
          unfold Walk.IsMaxlongPath at hp
          obtain H := SimpleGraph.Walk.IsPath.length_lt hp.1
          have : k < Fintype.card V := by omega
          have hk : k < Fintype.card V - 1 ∨ k = Fintype.card V - 1:= by omega
          rcases hk with (h1 | h2)
          · omega
          · have v_eq : v = b := by
              simp_all only [mem_neighborSet, tsub_lt_self_iff, _root_.zero_lt_one, and_true,
                tsub_pos_iff_lt, and_self]
              have len : Fintype.card V - 1 = p.length := by
                rw [← h_vertices_length, SimpleGraph.Walk.length_support]; simp
              rw [len] at h2
              simp only [k] at h2
              have eq1 : v = p.support[idxOf v p.support] := by simp
              have eq2 : b = p.support[p.length] := by
                obtain h := SimpleGraph.Walk.getVert_length p
                conv_lhs => rw [← h]
                rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                simp
              rw [eq1]
              conv_rhs => rw [eq2]; enter[2]; rw[← h2]
            simp_all only [mem_neighborSet, SimpleGraph.irrefl]
        let i : Fin (Fintype.card V -1) := ⟨k, this⟩
        refine ⟨i, ?_⟩
        calc
        p.support.get ⟨i.val, by omega⟩ = p.support.get ⟨k , by omega⟩ := by
          have : k - 1 + 1 = k := by omega
          simp_all only [mem_neighborSet, get_eq_getElem]
          simp only [i]
        _ = p.support.get ⟨k , by omega⟩ := by
          simp_all
        _ = v := by
          unfold Walk.IsMaxlongPath at hp
          obtain h := List.get_idxOf hp.1.support_nodup
          simp_all only [mem_neighborSet, get_eq_getElem]
          simp only [getElem_idxOf, k]
      rcases this with ⟨i, hi⟩
      have mem : i ∈ J := by
        unfold J
        simp only [get_eq_getElem, Finset.mem_filter, mem_univ, true_and]
        simp only [get_eq_getElem] at hi
        rw [SimpleGraph.adj_comm]
        simp_all only [mem_neighborSet]
      refine ⟨⟨i, mem⟩, ?_⟩
      simp only [List.get_eq_getElem, Subtype.mk.injEq, f]
      simp_all only [mem_neighborSet, List.get_eq_getElem]
    exact Equiv.ofBijective f ⟨hinj, hsurj⟩
  have h_disjoint : ¬ Disjoint I J := by
    intro H
    have h_total_size : #I + #J = G.degree a + G.degree b := by
      rw [h_card_I, h_card_J]
    obtain H' := h_ore a b h_ne h_ab
    have h_union_card : #(I ∪ J) = #I + #J := by
      rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at H
      rw [← Finset.card_union_eq_card_add_card] at H
      exact H
    have h_card_bound : I.card + J.card ≤ Fintype.card V - 1 := by
      have h_union_card : (I ∪ J).card ≤ Fintype.card V - 1 := by
        have : I ∪ J ⊆ Finset.univ := by
          intro x hx
          simp
        exact (Finset.card_le_univ _).trans_eq (Finset.card_fin _)
      obtain h := Finset.card_union I J
      rw [h] at h_union_card
      simp_all only [ne_eq, ge_iff_le, not_false_eq_true,
        card_union_of_disjoint]
    rw [h_total_size] at h_card_bound
    omega
  rw [Finset.not_disjoint_iff] at h_disjoint
  rcases h_disjoint with ⟨ k ,hxI, hxJ⟩
  use k
  let x := p.support.get ⟨k.val , by
        have : k.val < Fintype.card V - 1 := k.2
        omega⟩
  let y := p.support.get ⟨k.val + 1, by
        have : k.val < Fintype.card V - 1 := k.2
        omega⟩
  have h_adj1 : G.Adj a y := by simpa [I, Finset.mem_filter] using hxI
  have h_adj2 : G.Adj x b := by simpa [J, Finset.mem_filter] using hxJ
  have eq1 : x = p.getVert k := by
    simp only [get_eq_getElem, x]
    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
    have : p.length = p.support.length - 1 := by
      rw [SimpleGraph.Walk.length_support]; simp
    omega
  have eq2 : y = p.getVert (k + 1) := by
    simp only [get_eq_getElem, y]
    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
    have : p.length = p.support.length - 1 := by
      rw [SimpleGraph.Walk.length_support]; simp
    omega
  simp_all only [ne_eq, ge_iff_le, and_self]


/--
Under the Ore condition, the graph must be connected.
-/
theorem Ore_Connected {G : SimpleGraph V} [Fintype V] [G.LocallyFinite]
  {h_order : Fintype.card V ≥ 3} (h_ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ Fintype.card V) :
  G.Connected := by
  by_contra! h_not_conn
  have : ∃ (u v : V), u ≠ v ∧ ¬ G.Reachable u v := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable] at h_not_conn
    push_neg at h_not_conn
    have h_nonempty : Nonempty V := by
      have : 0 < Fintype.card V := by omega
      exact Fintype.card_pos_iff.mp this
    obtain ⟨u⟩ := h_nonempty
    rcases h_not_conn u with ⟨w, h_not_reachable⟩
    use u, w
    by_cases h_eq : u = w
    · exfalso
      rw [h_eq] at h_not_reachable
      simp only [Reachable.rfl, not_true_eq_false] at h_not_reachable
    · refine ⟨by simp only [ne_eq]; exact h_eq, h_not_reachable⟩
  rcases this with ⟨x, y, h_ne, h_not_reachable⟩
  have h_not_adj : ¬G.Adj x y := by
    intro h_adj
    apply SimpleGraph.Adj.reachable at h_adj
    contradiction
  have h_degree_sum := h_ore x y h_ne h_not_adj
  let n := Fintype.card V
  let comp_u := G.connectedComponentMk x
  let comp_v := G.connectedComponentMk y
  have comp_ne : comp_u ≠ comp_v := by
    simp only [ne_eq, ConnectedComponent.eq, comp_u, comp_v]
    exact h_not_reachable
  classical
  let U : Finset V := univ.filter fun w => G.connectedComponentMk w = comp_u
  let W : Finset V := univ.filter fun w => G.connectedComponentMk w = comp_v
  have U_disjoint_W : Disjoint U W := by
    simp only [ConnectedComponent.eq, U, comp_u, W, comp_v]
    simp_all only [ge_iff_le, ne_eq, not_false_eq_true]
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.Subset.antisymm
    · intro w hw
      rcases Finset.mem_inter.mp hw with ⟨hx_left, hx_right⟩
      simp_all only [mem_inter, and_self, Finset.mem_filter, mem_univ, true_and, notMem_empty]
      rw [SimpleGraph.reachable_comm] at hx_left
      obtain h := SimpleGraph.Reachable.trans hx_left hx_right
      contradiction
    · apply Finset.empty_subset
  have hU_nonempty : U.Nonempty := ⟨x, by simp only [ConnectedComponent.eq, Finset.mem_filter,
    mem_univ, Reachable.rfl, and_self, U, comp_u]⟩
  have hW_nonempty : W.Nonempty := ⟨y, by simp only [ConnectedComponent.eq, Finset.mem_filter,
    mem_univ, Reachable.rfl, and_self, W, comp_v]⟩
  let r := U.card
  let s := W.card
  have h_card_sum : r + s ≤ n := by
    calc
    r + s = (U ∪ W).card := by
      rw [Finset.card_union]
      simp only [r, s]
      rw [Finset.disjoint_iff_inter_eq_empty] at U_disjoint_W
      rw [U_disjoint_W]
      simp only [card_empty, tsub_zero]
    _ ≤ univ.card := Finset.card_le_univ _
    _ = n := by simp only [card_univ, n]
  have h_deg_u_bound : G.degree x ≤ r - 1 := by
    simp only [ConnectedComponent.eq, r, U, comp_u]
    have neighbors_in_U : G.neighborFinset x ⊆ U := by
      intro w hw
      simp_rw [mem_neighborFinset] at hw
      have comp_eq : G.connectedComponentMk w = comp_u := by
        simp only [ConnectedComponent.eq, comp_u]
        apply SimpleGraph.Adj.reachable
        rw [adj_comm]
        exact hw
      simp only [Finset.mem_filter, mem_univ, comp_eq, and_self, U]
    have not_self_neighbor : x ∉ G.neighborFinset x := by
      simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true]
    calc
      G.degree x = (G.neighborFinset x).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ (U.erase x).card := by
        apply Finset.card_le_card
        obtain  h := SimpleGraph.notMem_neighborFinset_self (v := x) (G := G)
        intro w hw
        rw [Finset.subset_iff] at neighbors_in_U
        obtain h := neighbors_in_U hw
        simp
        simp only [mem_neighborFinset] at hw
        obtain l := SimpleGraph.Adj.ne hw.symm
        refine ⟨by simp only [ne_eq] at l; exact l, h⟩
      _ = r - 1 := by
        simp only [r]
        apply Finset.card_erase_of_mem
        simp only [ConnectedComponent.eq, Finset.mem_filter, mem_univ, Reachable.rfl, and_self, U, comp_u]
    simp only [tsub_le_iff_right, r]
    rw [Nat.sub_add_cancel]
    · simp only [ConnectedComponent.eq, le_refl, U, comp_u]
    · simp only [ConnectedComponent.eq, U, comp_u] at hU_nonempty
      simp only [one_le_card]
      exact hU_nonempty
  have h_deg_v_bound : G.degree y ≤ s - 1 := by
    simp only [ConnectedComponent.eq, s, W, comp_v]
    have neighbors_in_W : G.neighborFinset y ⊆ W := by
      intro w hw
      simp_rw [mem_neighborFinset] at hw
      have comp_eq : G.connectedComponentMk w = comp_v := by
        simp only [ConnectedComponent.eq, comp_v]
        apply SimpleGraph.Adj.reachable
        rw [adj_comm]
        exact hw
      simp only [Finset.mem_filter, mem_univ, comp_eq, and_self, W]
    have not_self_neighbor : y ∉ G.neighborFinset y := by
      simp only [mem_neighborFinset, SimpleGraph.irrefl, not_false_eq_true]
    calc
      G.degree y = (G.neighborFinset y).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ (W.erase y).card := by
        apply Finset.card_le_card
        obtain  h := SimpleGraph.notMem_neighborFinset_self (v := x) (G := G)
        intro w hw
        rw [Finset.subset_iff] at neighbors_in_W
        obtain h := neighbors_in_W hw
        simp
        simp only [mem_neighborFinset] at hw
        obtain l := SimpleGraph.Adj.ne hw.symm
        refine ⟨by simp only [ne_eq] at l; exact l, h⟩
      _ = s - 1 := by
        simp only [s]
        apply Finset.card_erase_of_mem
        simp only [ConnectedComponent.eq, Finset.mem_filter, mem_univ, Reachable.rfl, and_self, W,
          comp_v]
    simp only [tsub_le_iff_right, s]
    rw [Nat.sub_add_cancel]
    · simp only [ConnectedComponent.eq, le_refl, W, comp_v]
    · simp only [ConnectedComponent.eq, W, comp_v] at hW_nonempty
      simp only [one_le_card]
      exact hW_nonempty
  have h_sum_bound : G.degree x + G.degree y ≤ n - 2 := by
    calc
      G.degree x + G.degree y ≤ (r - 1) + (s - 1) := add_le_add h_deg_u_bound h_deg_v_bound
      _ = (r + s) - 2 := by omega
      _ ≤ n - 2 := by omega
  have : n - 2 < n := by omega
  linarith [h_degree_sum, h_sum_bound]


/--
Let G be a graph of order n ≥ 3 that satisfies the Ore property. Then G has a Hamilton cycle.
-/
theorem Ore_theorem {G : SimpleGraph V} [Fintype V] [DecidableEq V] [G.LocallyFinite]
  {h_order : Fintype.card V ≥ 3} (h_ore : ∀ u v : V, u ≠ v → ¬ G.Adj u v → G.degree u + G.degree v ≥ Fintype.card V) :
  G.IsHamiltonian := by
  obtain hG := Ore_Connected (h_order := h_order) (h_ore := h_ore)
  rw [SimpleGraph.IsHamiltonian]
  intro h_card
  obtain ⟨a, b, p, h_maxpath⟩  := exists_maxilongmal_path (hG := hG) (G := G)
  obtain h_all_vertices := maximal_path_extends_or_hamiltonian (hG := hG) (p := p) (hp := h_maxpath) (h_order := h_order) (h_ore := h_ore)
  rcases Decidable.em (a = b) with h_eq | h
  · subst h_eq
    use a, p
    constructor
    · rw [SimpleGraph.Walk.isCycle_def]
      constructor
      · rw [SimpleGraph.Walk.isTrail_def]
        apply SimpleGraph.Walk.edges_nodup_of_support_nodup
        exact h_maxpath.1.support_nodup
      · constructor
        · intro h
          rw [h] at h_all_vertices
          have : Fintype.card V = 1 := by
            simp only [support_nil, List.mem_cons, not_mem_nil, or_false] at h_all_vertices
            apply Fintype.card_eq_one_of_forall_eq (i := a)
            omega
          omega
        · exact h_maxpath.1.support_nodup.tail
    · apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
      · apply SimpleGraph.Walk.IsPath.tail
        exact h_maxpath.1
      · intro v
        obtain h := h_all_vertices v
        rw [SimpleGraph.Walk.mem_support_iff] at h
        rcases h with ⟨h1, h2⟩
        · obtain h := h_all_vertices a
          simp_all only [end_mem_support]
        · rw [SimpleGraph.Walk.support_tail_of_not_nil]
          · omega
          · intro h
            rw [SimpleGraph.Walk.nil_iff_eq_nil] at h
            rw [h] at h_all_vertices
            have : Fintype.card V = 1 := by
              rw [Walk.support_nil] at h_all_vertices
              apply Fintype.card_eq_one_of_forall_eq (i := a)
              simp_all only [ge_iff_le, ne_eq, List.mem_cons, not_mem_nil, or_false, support_nil,
                List.tail_cons]
            omega
  classical
  rcases Decidable.em (G.Adj a b) with h_adj | h_adj
  · let cycle := p.concat h_adj.symm
    use a, cycle
    constructor
    · rw [SimpleGraph.Walk.isCycle_def]
      constructor
      · rw [SimpleGraph.Walk.isTrail_def]
        have h_p_trail : p.IsTrail := h_maxpath.1.isTrail
        rw [SimpleGraph.Walk.isTrail_def] at h_p_trail
        unfold cycle
        simp only [edges_concat, List.concat_eq_append]
        simp_all only [ge_iff_le, ne_eq]
        apply List.Nodup.append
        · exact h_p_trail
        · simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
          and_self]
        · by_contra! h_edge_in
          unfold Walk.IsMaxlongPath at h_maxpath
          have : p.length ≥ 2 := by
            have card_ge_three : 3 ≤ Fintype.card V := h_order
            obtain H := List.Nodup.length_le_card h_maxpath.1.support_nodup
            by_contra! h
            have : p.length = 1 ∨ p.length = 0 := by omega
            rcases this with (h1 | h2)
            · have h_path_len : p.length = Fintype.card V - 1 := by
                have h_support_size : p.support.toFinset.card = p.length + 1 := by
                  rw [List.toFinset_card_of_nodup h_maxpath.1.support_nodup, Walk.length_support]
                have h_all_in : (Finset.univ : Finset V) ⊆ p.support.toFinset := by
                  intro v hr
                  simp_all only [List.disjoint_singleton, Decidable.not_not, length_support,
                    Nat.reduceAdd, Nat.one_lt_ofNat, mem_univ, mem_toFinset]
                have h_eq : p.support.toFinset = Finset.univ := by
                  apply Finset.Subset.antisymm
                  · exact Finset.subset_univ _
                  · exact h_all_in
                have : Finset.card (Finset.univ : Finset V) = p.length + 1 := by
                  rw [← h_eq, h_support_size]
                rw [Finset.card_univ] at this
                omega
              simp_all only [length_support, Nat.reduceAdd,
                Nat.one_lt_ofNat, Nat.pred_eq_succ_iff, zero_add, Nat.add_one_sub_one,
                OfNat.ofNat_ne_one, not_false_eq_true, Nat.reduceLeDiff]
            · have : p.support.length = 1 := by simp_all only [nonpos_iff_eq_zero, length_support, zero_add, Nat.ofNat_pos]
              have h_path_len : p.length = Fintype.card V - 1 := by
                have h_support_size : p.support.toFinset.card = p.length + 1 := by
                  rw [List.toFinset_card_of_nodup h_maxpath.1.support_nodup, Walk.length_support]
                have h_all_in : (Finset.univ : Finset V) ⊆ p.support.toFinset := by
                  intro v hr
                  simp_all only [nonpos_iff_eq_zero,
                    Nat.ofNat_pos, length_support, zero_add, mem_univ, mem_toFinset]
                have h_eq : p.support.toFinset = Finset.univ := by
                  apply Finset.Subset.antisymm
                  · exact Finset.subset_univ _
                  · exact h_all_in
                have : Finset.card (Finset.univ : Finset V) = p.length + 1 := by
                  rw [← h_eq, h_support_size]
                rw [Finset.card_univ] at this
                omega
              omega
          have h : ¬p.Nil := by
            apply SimpleGraph.Walk.not_nil_of_ne
            omega
          obtain H := SimpleGraph.Walk.edge_firstDart p h
          simp only [List.disjoint_singleton, Decidable.not_not] at h_edge_in
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_edge_in
          have h_edge_val : p.edges.get i = s(a, b) := by
            simp_all only [ge_iff_le, get_eq_getElem, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
              and_false, Prod.swap_prod_mk, or_true]
          have h_verts := p.edges.get i
          rcases h_verts with (⟨h_vert_i, h_vert_i1⟩ | ⟨h_vert_i, h_vert_i1⟩)
          · have : i  < p.edges.length  := by omega
            obtain H := Walk.edge_get_verts (p := p) (hp := h_maxpath.1) i this
            by_cases hi0 : i.1= 0
            · simp_all only [ge_iff_le, get_eq_getElem, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
              and_false, Prod.swap_prod_mk, or_true, getVert_zero, zero_add, and_true]
              rcases H with (h1| h3)
              · simp_all only [not_true_eq_false]
              · have l: p.getVert p.length  = b := by simp_all only [length_edges, getVert_length]
                conv at l =>
                  right; rw [h3]
                have : p.length ≠ 1 := by omega
                rw [SimpleGraph.Walk.getVert_eq_getD_support, SimpleGraph.Walk.getVert_eq_getD_support] at l
                have : p.edges.length = p.support.length - 1:= by
                  rw [SimpleGraph.Walk.length_support]
                  simp
                rw [this] at i
                have l' :  p.support.length - 1 =p.length  := by
                  rw [SimpleGraph.Walk.length_support]
                  simp
                rw [SimpleGraph.Walk.length_edges] at this
                rename_i hl
                simp only [getD_eq_getElem?_getD, length_support, lt_add_iff_pos_right,
                  _root_.zero_lt_one, getElem?_pos, Option.getD_some] at l
                rw [<- List.getD_eq_getElem?_getD, List.getD_eq_getElem] at l
                · obtain Hl := List.Nodup.getElem_inj_iff h_maxpath.1.support_nodup (j := 1) (i := p.length)
                  have h_length_eq : p.length = 1 := Hl.mp l
                  omega
                · omega
            obtain H := Walk.edge_get_verts p h_maxpath.1 i this
            rw [hi] at H
            simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at H
            have : a = p.getVert 0  := by simp
            rcases H with (h1 | h2)
            · obtain h1'  := h1.2
              have l2 : i + 1 ≤ p.length := by
                rename_i l
                conv at l =>
                  enter[2]; rw [SimpleGraph.Walk.length_edges]
                omega
              obtain l1 := SimpleGraph.Walk.IsPath.getVert_eq_start_iff (p := p) (hp := h_maxpath.1) (i := (i + 1)) l2
              simp only [h1'.symm, Nat.add_eq_zero_iff, one_ne_zero, and_false, iff_false,
                not_true_eq_false] at l1
            · obtain h1'  := h2.2
              rw [Eq.comm] at h1'
              have l1' : i ≤ p.length := by
                rename_i l
                conv at l =>
                  enter[2]; rw [SimpleGraph.Walk.length_edges]
                omega
              have l2 : i + 1 ≤ p.length := by
                rename_i l
                conv at l =>
                  enter[2]; rw [SimpleGraph.Walk.length_edges]
                omega
              obtain l1 := SimpleGraph.Walk.IsPath.getVert_eq_end_iff (p := p) (hp := h_maxpath.1) (i := i + 1) l2
              conv at this =>
                left; rw [← h1']
              rw [SimpleGraph.Walk.getVert_eq_support_getElem p l1'] at this
              rw [SimpleGraph.Walk.getVert_eq_support_getElem p (by omega)] at this
              rw [List.Nodup.getElem_inj_iff] at this
              · contradiction
              · exact h_maxpath.1.support_nodup
      · constructor
        · intro h
          unfold cycle at h
          obtain h := SimpleGraph.Walk.concat_ne_nil p h_adj.symm h
          omega
        · simp only [support_concat, List.concat_eq_append, ne_eq, support_ne_nil,
            not_false_eq_true, List.tail_append_of_ne_nil, cycle]
          have h_nodup : p.support.Nodup := h_maxpath.1.support_nodup
          apply List.Nodup.append
          · exact h_maxpath.1.support_nodup.tail
          · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self]
          · simp_all only [ge_iff_le, ne_eq, List.disjoint_singleton]
            intro h
            obtain h' := SimpleGraph.Walk.support_eq_cons p
            rw [h'] at h_nodup
            simp only [Nodup, ne_eq, List.pairwise_cons] at h_nodup
            obtain h'' :=  h_nodup.1 a h
            contradiction
    · intro v
      have h_nodup : p.support.Nodup := h_maxpath.1.support_nodup
      have : cycle.tail.support.Nodup := by
        obtain h' := SimpleGraph.Walk.support_eq_cons cycle
        rw [SimpleGraph.Walk.support_tail_of_not_nil]
        · simp only [support_concat, List.concat_eq_append, ne_eq, support_ne_nil,
          not_false_eq_true, tail_append_of_ne_nil, cycle]
          rw [List.nodup_append]
          constructor
          · exact h_maxpath.1.support_nodup.tail
          · simp only [nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self,
            List.mem_cons, or_false, ne_eq, forall_eq, true_and]
            intro h_inter
            rw [SimpleGraph.Walk.support_eq_cons p] at h_nodup
            simp only [Nodup, ne_eq, List.pairwise_cons] at h_nodup
            obtain h'' := h_nodup.1 a
            intro h h'
            simp_all only [ge_iff_le, ne_eq, not_true_eq_false, imp_false]
        · rw [SimpleGraph.Walk.nil_iff_eq_nil]
          simp only [cycle]
          intro h_nil
          rw [SimpleGraph.Walk.concat_eq_append] at h_nil
          rw [← SimpleGraph.Walk.nil_iff_eq_nil, SimpleGraph.Walk.nil_append_iff] at h_nil
          simp_all only [ge_iff_le, ne_eq, not_nil_cons, and_false]
      rw [List.nodup_iff_count_eq_one] at this
      have h : v ∈ cycle.tail.support := by
        have : cycle.tail.support = p.support.tail ++ [a] := by
          unfold cycle
          rw [SimpleGraph.Walk.support_tail_of_not_nil]
          · simp
          · simp only [Walk.concat, nil_append_iff, not_nil_cons, and_false, not_false_eq_true]
        rw [this]
        obtain H := h_all_vertices v
        simp only [mem_append, List.mem_cons, not_mem_nil, or_false]
        rw [SimpleGraph.Walk.mem_support_iff] at H
        exact H.symm
      simp_all only [ge_iff_le, ne_eq]
  · have h_ne : a ≠ b := by omega
    obtain H := ore_adjacent (hG := hG) (p := p) (hp := h_maxpath) (h_order := h_order) (h_ne := h_ne) (h_ab := h_adj) (h_ore := h_ore)
    rcases H with ⟨k, ⟨h1, h2⟩⟩
    have hk' : p.getVert (k + 1) ∈ p.reverse.support := by simp
    have hk : p.getVert k ∈ p.support := by simp
    let eaxy_ksucc_b : G.Walk b (p.getVert (k + 1)) := (p.reverse.takeUntil (p.getVert (k + 1)) hk')
    let eaxy_ak : G.Walk a (p.getVert k) := p.takeUntil (p.getVert k) hk
    let cycle : G.Walk (p.getVert k) (p.getVert k) := (Walk.cons h2 eaxy_ksucc_b).append (Walk.cons h1.symm eaxy_ak)
    use p.getVert k
    use cycle
    have h_path_len : p.length = Fintype.card V - 1 := by
      have h_support_size : p.support.toFinset.card = p.length + 1 := by
        rw [List.toFinset_card_of_nodup h_maxpath.1.support_nodup, Walk.length_support]
      have h_all_in : (Finset.univ : Finset V) ⊆ p.support.toFinset := by
        intro v hr
        simp_all only [ge_iff_le, ne_eq, not_false_eq_true, mem_univ, mem_toFinset]
      have h_eq : p.support.toFinset = Finset.univ := by
        apply Finset.Subset.antisymm
        · exact Finset.subset_univ _
        · exact h_all_in
      have : Finset.card (Finset.univ : Finset V) = p.length + 1 := by
        rw [← h_eq, h_support_size]
      rw [Finset.card_univ] at this
      omega
    have H5 : (eaxy_ksucc_b.append (Walk.cons h1.symm eaxy_ak)).support.Nodup := by
      obtain H := List.nodup_append' (l₁ := eaxy_ksucc_b.support) (l₂ := (Walk.cons h1.symm eaxy_ak).support.tail)
      have : (eaxy_ksucc_b.append (Walk.cons h1.symm eaxy_ak)).support.Nodup =
        (eaxy_ksucc_b.support ++ ((Walk.cons h1.symm eaxy_ak)).support.tail).Nodup := by
        rw [Walk.support_append]
      rw [this, H]
      constructor
      · simp only [eaxy_ksucc_b]
        rw [← SimpleGraph.Walk.isPath_def]
        apply SimpleGraph.Walk.IsPath.takeUntil
        · simp only [isPath_reverse_iff]
          exact h_maxpath.1
      · constructor
        · simp only [support_cons, List.tail_cons, eaxy_ak]
          rw [← SimpleGraph.Walk.isPath_def]
          apply SimpleGraph.Walk.IsPath.takeUntil
          exact h_maxpath.1
        · simp only [support_cons, List.tail_cons, eaxy_ksucc_b, eaxy_ak]
          have H4 : (p.reverse.takeUntil (p.getVert (k + 1)) hk').support.Disjoint
            ((p.takeUntil (p.getVert k) hk)).support := by
            rw [← List.inter_eq_nil_iff_disjoint]
            rw [← List.toFinset_eq_empty_iff]
            simp only [toFinset_inter]
            apply Finset.Subset.antisymm
            · intro x hx
              rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
              have h1 : p.getVert k ∈ p.support := by omega
              simp only [mem_toFinset] at hx_left
              simp only [mem_toFinset] at hx_right
              have h_indices_left : ∃ j , p.reverse.getVert j = x ∧ j ≤ p.length - (k + 1) := by
                rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_left
                rcases hx_left with ⟨j , hj, hj_len⟩
                rw [SimpleGraph.Walk.getVert_takeUntil] at hj
                · use j
                  have h1 : p.getVert (k + 1) ∈ p.reverse.support := by
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                    · simp only [support_reverse, mem_reverse, getElem_mem]
                    · have : k + 1 ≤ p.length := by
                        have : p.getVert (k + 1) ∈ p.reverse.support := by omega
                        obtain l := SimpleGraph.Walk.length_takeUntil_le p.reverse this
                        omega
                      omega
                  have : p.reverse.getVert (p.reverse.takeUntil (p.getVert (k + 1)) h1).length =
                    p.reverse.getVert (p.length - (k + 1)) := by
                    rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
                    rw [Nat.sub_sub_self]
                    have l': k  < p.length := by
                      omega
                    linarith
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                  · have l : (p.length - (k + 1)) ≤ p.reverse.length := by
                      simp
                    conv at this =>
                      right;
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l]
                      rfl
                    rw [List.Nodup.getElem_inj_iff] at this
                    · rw [this] at hj_len
                      refine ⟨hj, hj_len⟩
                    · simp only [support_reverse, nodup_reverse]
                      exact h_maxpath.1.support_nodup
                  · apply SimpleGraph.Walk.length_takeUntil_le
                · exact hj_len
              · have h_indices_right : ∃ j, p.getVert j = x ∧ j ≤ k := by
                  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx_right
                  rcases hx_right  with ⟨j , hj, hj_len⟩
                  rw [SimpleGraph.Walk.getVert_takeUntil] at hj
                  · use j
                    simp_all only [ge_iff_le, ne_eq, not_false_eq_true, support_cons,
                      List.tail_cons, eq_iff_iff, mem_inter, mem_toFinset, true_and]
                    have l : k ≤ p.length := by
                      omega
                    have h1 : p.getVert k ∈ p.support := by
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem]
                      · simp only [getElem_mem]
                      · omega
                    have : p.getVert (p.takeUntil (p.getVert k) h1).length =  p.getVert k := by
                      rw [SimpleGraph.Walk.getVert_length_takeUntil]
                    rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                    conv at this =>
                      right;
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                      rfl
                    · rw [List.Nodup.getElem_inj_iff] at this
                      · rw [this] at hj_len
                        exact hj_len
                      · exact h_maxpath.1.support_nodup
                    · apply SimpleGraph.Walk.length_takeUntil_le
                  · exact hj_len
                rcases h_indices_left with ⟨k₁, hk₁_eq, hk₁_ge⟩
                rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                rw [SimpleGraph.Walk.getVert_reverse] at hk₁_eq
                rw [← hk₂_eq] at hk₁_eq
                have hk_eq : k₁ =  p.length - k₂ := by
                  have l1 : (p.length - k₁) ≤ p.length := by omega
                  have l2 : k₂ ≤  p.length := by omega
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem p l1] at hk₁_eq
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem p l2] at hk₁_eq
                  rw [List.Nodup.getElem_inj_iff] at hk₁_eq
                  · omega
                  · exact h_maxpath.1.support_nodup
                rw [hk_eq] at hk₁_ge
                omega
            · apply Finset.empty_subset
          exact H4
    constructor
    · rw [SimpleGraph.Walk.isCycle_def]
      constructor
      · rw [SimpleGraph.Walk.isTrail_def]
        have h_p_trail : p.IsTrail := h_maxpath.1.isTrail
        rw [SimpleGraph.Walk.isTrail_def] at h_p_trail
        unfold cycle
        simp only [Walk.cons_append, edges_cons, edges_append, nodup_cons, mem_append,
          List.mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, not_or, not_and]
        constructor
        · constructor
          · simp only [eaxy_ksucc_b]
            have hp_path : (p.reverse.takeUntil (p.getVert (k + 1)) hk').IsPath := by
              apply SimpleGraph.Walk.IsPath.takeUntil
              simp only [isPath_reverse_iff]
              exact h_maxpath.1
            by_contra h_edge_in
            obtain H := SimpleGraph.Walk.fst_mem_support_of_mem_edges (p := (p.reverse.takeUntil (p.getVert (k + 1)) hk')) h_edge_in
            rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at H
            have : p.reverse.getVert (p.reverse.takeUntil (p.getVert (k + 1)) hk').length = p.reverse.getVert (p.length - (k + 1)) := by
              rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
              rw [Nat.sub_sub_self]
              rw [h_path_len]
              omega
            have l1 : (p.reverse.takeUntil (p.getVert (k + 1)) hk').length ≤ p.reverse.length := by
              apply SimpleGraph.Walk.length_takeUntil_le
            have l2 : (p.length - (k + 1)) ≤ p.reverse.length := by simp
            rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l1] at this
            conv at this =>
              right;
              rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l2]
            rw [List.Nodup.getElem_inj_iff] at this
            · rcases H with ⟨n, h1, h2⟩
              rw [this] at h2
              have : p.getVert k = p.reverse.getVert (p.length - k) := by
                rw [SimpleGraph.Walk.getVert_reverse, Nat.sub_sub_self]
                omega
              rw [this] at h1
              rw [SimpleGraph.Walk.getVert_takeUntil] at h1
              · have l1 : n ≤ p.reverse.length := by
                  simp only [Walk.length_reverse]
                  omega
                have l2 : (p.length - k) ≤ p.reverse.length := by simp
                rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l1] at h1
                rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l2] at h1
                rw [List.Nodup.getElem_inj_iff] at h1
                · rw [h1] at h2
                  omega
                · simp only [support_reverse, nodup_reverse]
                  exact h_maxpath.1.support_nodup
              · omega
            · simp only [support_reverse, nodup_reverse]
              exact h_maxpath.1.support_nodup
          · constructor
            · constructor
              · intro h
                by_contra
                rw [this] at h_ne
                simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
              · intro h
                by_contra
                have l : k < p.length := by omega
                obtain h' := SimpleGraph.Walk.adj_getVert_succ p l
                simp only [h] at h'
                rw [← this] at h'
                contradiction
            · simp only [eaxy_ak]
              have hp_path :(p.takeUntil (p.getVert k) hk).IsPath := by
                apply SimpleGraph.Walk.IsPath.takeUntil
                exact h_maxpath.1
              by_contra h_edge_in
              obtain H := SimpleGraph.Walk.snd_mem_support_of_mem_edges (p := (p.takeUntil (p.getVert ↑k) hk)) h_edge_in
              rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at H
              rcases H with ⟨n, h1, h2⟩
              rw [SimpleGraph.Walk.getVert_takeUntil] at h1
              · rw [SimpleGraph.Walk.IsPath.getVert_eq_end_iff] at h1
                · have l : p.getVert k ∈ p.support := by omega
                  have len_take_k : (p.takeUntil (p.getVert k) l).length = k := by
                    apply Eq.symm
                    rw [←  SimpleGraph.Walk.getVert_le_length_takeUntil_eq_iff]
                    omega
                  rw [h1, len_take_k] at h2
                  omega
                · exact h_maxpath.1
                · have h : p.getVert k ∈ p.support := by omega
                  obtain hl := SimpleGraph.Walk.length_takeUntil_le p h
                  linarith
              · exact h2
        · rw [← SimpleGraph.Walk.edges_cons (h := by rw [adj_comm] at h1; exact h1)]
          rw [← SimpleGraph.Walk.edges_append]
          apply SimpleGraph.Walk.edges_nodup_of_support_nodup
          exact H5
      · constructor
        · unfold cycle
          simp only [Walk.cons_append, ne_eq, reduceCtorEq, not_false_eq_true, eaxy_ksucc_b]
        · simp only [Walk.cons_append, support_cons, List.tail_cons, cycle]
          exact H5
    · unfold cycle
      apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
      · rw [SimpleGraph.Walk.isPath_def]
        obtain H := List.nodup_append'  (l₁ := (Walk.cons h2 eaxy_ksucc_b).tail.support) (l₂ := ((Walk.cons h1.symm eaxy_ak)).tail.support)
        rw [SimpleGraph.Walk.support_tail_of_not_nil,SimpleGraph.Walk.tail_support_append]
        · rw [← SimpleGraph.Walk.support_tail_of_not_nil, ← SimpleGraph.Walk.support_tail_of_not_nil]
          · rw [H]
            constructor
            · simp only [getVert_cons_succ, Walk.tail_cons, support_copy, eaxy_ksucc_b]
              rw [← SimpleGraph.Walk.isPath_def]
              apply SimpleGraph.Walk.IsPath.takeUntil
              simp only [isPath_reverse_iff]
              exact h_maxpath.1
            · constructor
              · simp only [getVert_cons_succ, Walk.tail_cons, support_copy, eaxy_ak]
                rw [← SimpleGraph.Walk.isPath_def]
                apply SimpleGraph.Walk.IsPath.takeUntil
                exact h_maxpath.1
              · simp only [getVert_cons_succ, Walk.tail_cons, support_copy, eaxy_ksucc_b, eaxy_ak]
                have H4 : (p.reverse.takeUntil (p.getVert (k + 1)) hk').support.Disjoint
                  ((p.takeUntil (p.getVert k) hk)).support := by
                  rw [← List.inter_eq_nil_iff_disjoint]
                  rw [← List.toFinset_eq_empty_iff]
                  simp only [toFinset_inter]
                  apply Finset.Subset.antisymm
                  · intro x hx
                    rcases Finset.mem_inter.mp hx with ⟨hx_left, hx_right⟩
                    have h1 : p.getVert k ∈ p.support := by omega
                    simp only [mem_toFinset] at hx_left
                    simp only [mem_toFinset] at hx_right
                    have h_indices_hv: ∃ j, p.getVert j = x ∧ j ≥ k + 1 ∧ j ≤ p.length:= by
                      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hx_left
                      rcases hx_left  with ⟨j , hj, hj_len⟩
                      have len : (p.takeUntil (p.getVert k) hk).length = k := by
                          have : p.getVert (p.takeUntil (p.getVert k) hk).length = p.getVert k := by
                            rw [SimpleGraph.Walk.getVert_length_takeUntil]
                          rw [SimpleGraph.Walk.getVert_eq_support_getElem p] at this
                          · have l : k ≤ p.length := by omega
                            conv at this =>
                              right;
                              rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                            rw [List.Nodup.getElem_inj_iff] at this
                            · exact this
                            · exact h_maxpath.1.support_nodup
                          · apply SimpleGraph.Walk.length_takeUntil_le
                      · use (p.length - j)
                        · rw [SimpleGraph.Walk.getVert_takeUntil, SimpleGraph.Walk.getVert_reverse] at hj
                          · have len : (p.reverse.takeUntil (p.getVert (k + 1)) hk').length = p.length - (k + 1) := by
                              have : p.reverse.getVert (p.reverse.takeUntil (p.getVert (k + 1)) hk').length =
                                p.reverse.getVert (p.length - (k + 1)) := by
                                rw [SimpleGraph.Walk.getVert_length_takeUntil, SimpleGraph.Walk.getVert_reverse]
                                rw [Nat.sub_sub_self]
                                have l': k + 1 ≤ p.length := by
                                  omega
                                omega
                              rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                              · have l : (p.length - (k + 1)) ≤ p.reverse.length := by
                                  simp only [Walk.length_reverse, tsub_le_iff_right,
                                    le_add_iff_nonneg_right, zero_le]
                                conv at this =>
                                  right;
                                  rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l]
                                  rfl
                                rw [List.Nodup.getElem_inj_iff] at this
                                · exact this
                                · simp only [support_reverse, nodup_reverse]
                                  exact h_maxpath.1.support_nodup
                              · apply SimpleGraph.Walk.length_takeUntil_le
                            refine ⟨hj, ?_⟩
                            rw [len] at hj_len
                            omega
                          · omega
                    have h_indices_right : ∃ j, p.getVert j = x ∧ j ≤ k := by
                      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hx_right
                      rcases hx_right with ⟨j , hj, hj_len⟩
                      rw [SimpleGraph.Walk.getVert_takeUntil] at hj
                      · use j
                        simp_all only [ge_iff_le, ne_eq, not_false_eq_true, getVert_cons_succ,
                          Walk.tail_cons, support_copy, mem_inter, mem_toFinset, true_and]
                        have h1 : p.getVert k ∈ p.support := by omega
                        have : p.getVert (p.takeUntil (p.getVert k) h1).length =  p.getVert k := by
                          rw [SimpleGraph.Walk.getVert_length_takeUntil]
                        rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                        · have l : k ≤ p.length := by omega
                          conv at this =>
                            right;
                            rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                            rfl
                          rw [List.Nodup.getElem_inj_iff] at this
                          · rw [this] at hj_len
                            exact hj_len
                          · exact h_maxpath.1.support_nodup
                        · apply SimpleGraph.Walk.length_takeUntil_le
                      · exact hj_len
                    rcases h_indices_hv with ⟨k₁, hk₁_eq, hk₁_ge⟩
                    rcases h_indices_right with ⟨k₂, hk₂_eq, hk₂_le⟩
                    rw [← hk₂_eq] at hk₁_eq
                    have hk_eq : k₁ = k₂ := by
                      have l : k₁ ≤ p.length := by omega
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem p l] at hk₁_eq
                      have l': k₂ ≤  p.length := by
                        omega
                      have l : k ≤ p.length := by omega
                      have l : k₁ ≤ p.length := by omega
                      rename_i hk₂_eq'
                      conv at hk₁_eq =>
                        rw [SimpleGraph.Walk.getVert_eq_support_getElem p l']
                      rw [List.Nodup.getElem_inj_iff] at hk₁_eq
                      · omega
                      · exact h_maxpath.1.support_nodup
                    rw [hk_eq] at hk₁_ge
                    omega
                  · apply Finset.empty_subset
                exact H4
          · simp only [not_nil_cons, not_false_eq_true, eaxy_ak]
          · simp only [not_nil_cons, not_false_eq_true]
        · simp only [Walk.cons_append, not_nil_cons, not_false_eq_true]
      · intro v
        obtain hv := h_all_vertices v
        have hv_subset : p.support ⊆ ((Walk.cons h2 eaxy_ksucc_b).append (Walk.cons h1.symm eaxy_ak)).tail.support := by
          simp only [Walk.cons_append, getVert_cons_succ, Walk.tail_cons, support_copy,
            eaxy_ksucc_b, eaxy_ak]
          have hk : p.getVert k ∈ p.support := by omega
          rw [← SimpleGraph.Walk.concat_append, SimpleGraph.Walk.support_append]
          rw [SimpleGraph.Walk.support_concat]
          simp only [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append]
          rw [← SimpleGraph.Walk.support_eq_cons]
          have hp_split : p.support = ((p.takeUntil (p.getVert k) hk).append (p.dropUntil (p.getVert k) hk)).support := by
            obtain H := SimpleGraph.Walk.take_spec p hk
            conv_lhs => rw [← H]
          rw [hp_split]
          rw [← List.append_eq_has_append]
          rw [SimpleGraph.Walk.support_append]
          rw [← List.append_eq_has_append]
          simp only [append_eq, append_subset, List.Subset.refl, subset_append_of_subset_right,
            true_and]
          apply List.subset_append_of_subset_left
          rw [List.subset_def]
          intro v hv
          have h_indices_hv: ∃ j, p.getVert j = v ∧ j ≥ k + 1 ∧ j ≤ p.length:= by
            rw [← SimpleGraph.Walk.support_tail_of_not_nil] at hv
            · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hv
              rcases hv with ⟨j , hj, hj_len⟩
              rw [SimpleGraph.Walk.getVert_tail] at hj
              have : (p.dropUntil (p.getVert ↑k) hk).tail.length =
                (p.dropUntil (p.getVert ↑k) hk).length -1 := by
                nth_rw 2 [← SimpleGraph.Walk.length_tail_add_one]
                · simp only [add_tsub_cancel_right]
                · apply SimpleGraph.Walk.not_nil_of_ne
                  by_contra H
                  simp only [H, SimpleGraph.irrefl] at h2
              rw [this] at hj_len
              have len : (p.takeUntil (p.getVert k) hk).length = k := by
                  have : p.getVert (p.takeUntil (p.getVert k) hk).length =  p.getVert k := by
                    rw [SimpleGraph.Walk.getVert_length_takeUntil]
                  rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
                  · have l : k ≤ p.length := by omega
                    conv at this =>
                      right;
                      rw [SimpleGraph.Walk.getVert_eq_support_getElem p l]
                      rfl
                    rw [List.Nodup.getElem_inj_iff] at this
                    · exact this
                    · exact h_maxpath.1.support_nodup
                  · apply SimpleGraph.Walk.length_takeUntil_le
              use (k + j + 1)
              have hj_in : p.getVert (k + j + 1) ∈ p.support := by
                apply SimpleGraph.Walk.getVert_mem_support
              obtain drop_len := getVert_length_dropUntil hj_in
              rw [SimpleGraph.Walk.getVert_reverse] at drop_len
              rw [← drop_len]
              rw [← SimpleGraph.Walk.getVert_reverse]
              rw [getVert_length_dropUntil]
              rw [getVert_dropUntil hk len.symm, ← Nat.add_assoc] at hj
              · refine ⟨hj, ?_⟩
                · have : (p.dropUntil (p.getVert ↑k) hk).length = p.length -
                    ((p.takeUntil (p.getVert k) hk).length) := by
                    have len : p.length = (p.dropUntil (p.getVert ↑k) hk).length + (p.takeUntil (p.getVert ↑k) hk).length := by
                      rw [add_comm]
                      rw [← SimpleGraph.Walk.length_edges, ← SimpleGraph.Walk.length_edges,← SimpleGraph.Walk.length_edges]
                      rw [ ← List.length_append]
                      conv_rhs => enter [1]; rw [← SimpleGraph.Walk.edges_append (p := p.takeUntil (p.getVert ↑k) hk), SimpleGraph.Walk.take_spec]
                    omega
                  rw [this, len] at hj_len
                  omega
              · omega
            · apply SimpleGraph.Walk.not_nil_of_ne
              by_contra H
              simp only [H, SimpleGraph.irrefl] at h2
          rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
          rcases h_indices_hv with ⟨j, h1, h2⟩
          use (p.length - j)
          have len : (p.reverse.takeUntil (p.getVert (k + 1)) hk').length =
            p.length - (k + 1) := by
            have hksucc : p.getVert (k + 1) ∈ p.reverse.support := by
              simp only [support_reverse, mem_reverse, getVert_mem_support]
            have : p.reverse.getVert (p.reverse.takeUntil (p.getVert (k + 1)) hksucc).length =  p.reverse.getVert (p.length - (k + 1)) := by
              rw [SimpleGraph.Walk.getVert_length_takeUntil]
              rw [SimpleGraph.Walk.getVert_reverse, Nat.sub_sub_self]
              omega
            rw [SimpleGraph.Walk.getVert_eq_support_getElem] at this
            · have l : p.length - (k + 1) ≤ p.reverse.length := by simp
              conv at this =>
                right;
                rw [SimpleGraph.Walk.getVert_eq_support_getElem p.reverse l]
                rfl
              rw [List.Nodup.getElem_inj_iff] at this
              · omega
              · simp only [support_reverse, nodup_reverse]
                exact h_maxpath.1.support_nodup
            · apply SimpleGraph.Walk.length_takeUntil_le
          constructor
          · rw [SimpleGraph.Walk.getVert_takeUntil]
            · rw [SimpleGraph.Walk.getVert_reverse, Nat.sub_sub_self]
              · exact h1
              · omega
            · omega
          · omega
        rw [List.subset_def ] at hv_subset
        exact hv_subset hv
