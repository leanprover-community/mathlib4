/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Card

/-!
# Connectivity in a finite graph

This file provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.
-/

public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem ConnectedComponent.card_le_card_of_le [Finite V] {G G' : SimpleGraph V} (h : G ≤ G') :
    Nat.card G'.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  Nat.card_le_card_of_surjective _ <| ConnectedComponent.surjective_map_ofLE h

/-!
### Deciding reachability by breadth-first search

This section provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.

The algorithm is as follows: we maintain the list of vertices visited so far along with the list of
vertices remaining to be visited, and we repeatedly move to the former the vertices of the latter
that are adjacent to the *frontier*, namely the vertices visited during the previous round. We stop
as soon as a round visits no new vertex. Since a vertex enters the frontier at most once, a search
costs `O(|V| ^ 2)` adjacency tests.

Vertices `u` and `v` are then reachable if `v` lies in the BFS-constructed list of vertices
reachable from `u`, and a graph is (pre)connected iff it's non-empty and (/empty or) every vertex
lies in the reachability list of an arbitrarily-chosen vertex. Since the search visits each vertex
at most once, the latter is checked by comparing the length of the reachability list to the number
of vertices, which is cheaper than testing membership of every vertex.
-/

section BFS
variable [DecidableRel G.Adj] {l s acc : List V} {n : ℕ} {u v w : V}

omit [DecidableRel G.Adj] in
/-- A list of vertices closed under adjacency is closed under reachability. -/
private lemma Reachable.mem_of_forall_adj_mem (huv : G.Reachable u v)
    (hs : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s) : u ∈ s → v ∈ s := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact id
  | cons hxy _ ih => exact fun hu ↦ ih (hs _ hu _ hxy)

/-- One round of breadth-first search: `G.bfsStep s l acc` prepends to `acc` the vertices of the
list `l` of vertices remaining to be visited that are adjacent to some vertex of the frontier `s`,
namely the vertices getting visited during this round. -/
def bfsStep (G : SimpleGraph V) [DecidableRel G.Adj] (s : List V) : List V → List V → List V
  | [], acc => acc
  | w :: l, acc => G.bfsStep s l (if s.any (G.Adj · w) then w :: acc else acc)

@[simp, grind =]
lemma mem_bfsStep : ∀ {l acc}, w ∈ G.bfsStep s l acc ↔ (w ∈ l ∧ ∃ v ∈ s, G.Adj v w) ∨ w ∈ acc
  | [], acc => by simp [bfsStep]
  | x :: l, acc => by rw [bfsStep, mem_bfsStep]; grind

lemma bfsStep_eq_reverse_filter_append :
    ∀ {l acc}, G.bfsStep s l acc = (l.filter fun w ↦ s.any (G.Adj · w)).reverse ++ acc
  | [], acc => by simp [bfsStep]
  | x :: l, acc => by
    rw [bfsStep, bfsStep_eq_reverse_filter_append, List.filter_cons]
    split <;> simp

lemma nodup_bfsStep_append (hl : l.Nodup) (hacc : acc.Nodup) (h : ∀ x ∈ l, x ∉ acc) :
    (G.bfsStep s l [] ++ acc).Nodup := by
  rw [bfsStep_eq_reverse_filter_append, List.append_nil]
  exact List.Nodup.append (List.nodup_reverse.2 (hl.filter _)) hacc fun x hx hx' ↦
    h x (List.mem_of_mem_filter (List.mem_reverse.1 hx)) hx'

/-- Iterate breadth-first search at most `n` times, stopping as soon as a round visits no new
vertex.

`G.bfsIterate n s l acc` is the list of visited vertices, where `s` is the current frontier, `l` the
list of vertices remaining to be visited and `acc` the list of already visited vertices. -/
def bfsIterate (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → List V → List V → List V → List V
  | 0, _, _, acc => acc
  | n + 1, s, l, acc =>
    let s' := G.bfsStep s l []
    if s'.isEmpty then acc
    else G.bfsIterate n s' (l.filter fun w ↦ !s.any (G.Adj · w)) (s' ++ acc)

/-- Breadth-first search only visits vertices reachable from `u`, assuming the frontier is made of
visited vertices and that all visited vertices are reachable from `u`. -/
lemma reachable_of_mem_bfsIterate (hs : ∀ x ∈ s, x ∈ acc) (hacc : ∀ x ∈ acc, G.Reachable u x)
    (hv : v ∈ G.bfsIterate n s l acc) : G.Reachable u v := by
  induction n generalizing s l acc with
  | zero => exact hacc _ hv
  | succ n ih =>
  simp only [bfsIterate] at hv
  split_ifs at hv with h
  · exact hacc _ hv
  refine ih (fun x hx ↦ List.mem_append_left _ hx) (fun x hx ↦ ?_) hv
  rw [List.mem_append] at hx
  obtain hx | hx := hx
  · obtain ⟨-, y, hy, hyx⟩ | hx := mem_bfsStep.1 hx
    · exact (hacc _ (hs _ hy)).trans hyx.reachable
    · simp at hx
  · exact hacc _ hx

/-- Breadth-first search visits all vertices reachable from `u`, assuming it is run for at least as
many rounds as there are vertices remaining to be visited, that every vertex is either visited or
remaining, that `u` is visited and that all neighbours of a visited vertex outside of the frontier
are themselves visited. -/
lemma mem_bfsIterate_of_reachable (hn : l.length ≤ n) (hu : u ∈ acc) (hl : ∀ x, x ∈ l ∨ x ∈ acc)
    (hacc : ∀ x ∈ acc, x ∉ s → ∀ y, G.Adj x y → y ∈ acc) (hv : G.Reachable u v) :
    v ∈ G.bfsIterate n s l acc := by
  induction n generalizing s l acc with
  | zero =>
    rw [Nat.le_zero, List.length_eq_zero_iff] at hn
    subst hn
    simpa only [bfsIterate] using (hl v).resolve_left (by simp)
  | succ n ih =>
  simp only [bfsIterate]
  split_ifs with h
  · -- No new vertex got visited, hence the visited vertices are closed under adjacency.
    rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem] at h
    refine hv.mem_of_forall_adj_mem (fun x hx y hxy ↦ ?_) hu
    by_cases hxs : x ∈ s
    · exact (hl y).resolve_left fun hy ↦ h y <| mem_bfsStep.2 <| .inl ⟨hy, x, hxs, hxy⟩
    · exact hacc _ hx hxs _ hxy
  -- Some new vertex got visited, hence there is one less vertex remaining to be visited.
  rw [List.isEmpty_iff] at h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hwl, hws⟩ : w ∈ l ∧ ∃ z ∈ s, G.Adj z w := by simpa using hw
  refine ih ?_ (List.mem_append_right _ hu) (fun x ↦ ?_) (fun x hx hxs y hxy ↦ ?_)
  · have : (l.filter fun w ↦ !s.any (G.Adj · w)).length < l.length :=
      List.length_filter_lt_length_iff_exists.2 ⟨w, hwl, by simpa using hws⟩
    lia
  · obtain hx | hx := hl x
    · by_cases hxs : ∃ z ∈ s, G.Adj z x
      · exact .inr <| List.mem_append_left _ <| mem_bfsStep.2 <| .inl ⟨hx, hxs⟩
      · exact .inl <| List.mem_filter.2 ⟨hx, by simpa using hxs⟩
    · exact .inr <| List.mem_append_right _ hx
  · simp only [List.mem_append, hxs, false_or, mem_bfsStep, List.not_mem_nil, or_false] at hx ⊢
    by_cases hxs' : x ∈ s
    · obtain hy | hy := hl y
      · exact .inl ⟨hy, x, hxs', hxy⟩
      · exact .inr hy
    · exact .inr <| hacc _ hx hxs' _ hxy

/-- Breadth-first search only visits vertices that were remaining to be visited or already
visited. -/
lemma mem_or_mem_of_mem_bfsIterate (hv : v ∈ G.bfsIterate n s l acc) : v ∈ l ∨ v ∈ acc := by
  induction n generalizing s l acc with
  | zero => exact .inr hv
  | succ n ih =>
    simp only [bfsIterate] at hv
    split_ifs at hv with h
    · exact .inr hv
    obtain hv | hv := ih hv
    · exact .inl <| List.mem_of_mem_filter hv
    · rw [List.mem_append] at hv
      exact hv.imp (fun hv ↦ (mem_bfsStep.1 hv).elim And.left (by simp)) id

/-- Breadth-first search visits no vertex twice, assuming the lists of remaining and of visited
vertices are themselves duplicate-free and disjoint. -/
lemma nodup_bfsIterate (hl : l.Nodup) (hacc : acc.Nodup) (h : ∀ x ∈ l, x ∉ acc) :
    (G.bfsIterate n s l acc).Nodup := by
  induction n generalizing s l acc with
  | zero => exact hacc
  | succ n ih =>
    simp only [bfsIterate]
    split_ifs with h'
    · exact hacc
    refine ih (hl.filter _) (nodup_bfsStep_append hl hacc h) fun x hx hx' ↦ ?_
    rw [List.mem_filter] at hx
    obtain hx' | hx' := List.mem_append.1 hx'
    · simp only [mem_bfsStep, List.not_mem_nil, or_false] at hx'
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hx
      exact absurd hx'.2 (by simpa using hx.2)
    · exact h _ hx.1 hx'

variable [DecidableEq V]

variable (G) in
/-- The list of vertices in `l` reachable from `u` via vertices of `l`, computed by breadth-first
search through the list `l` of all vertices. -/
def bfsList (u : V) (l : List V) : List V := G.bfsIterate (l.length - 1) [u] (l.erase u) [u]

lemma mem_of_mem_bfsList (hu : u ∈ l) (hv : v ∈ G.bfsList u l) : v ∈ l := by
  obtain hv | hv := mem_or_mem_of_mem_bfsIterate hv
  · exact List.erase_subset hv
  · rwa [List.mem_singleton.1 hv]

lemma nodup_bfsList (hl : l.Nodup) : (G.bfsList u l).Nodup :=
  nodup_bfsIterate (hl.erase _) (List.nodup_singleton _) fun x hx ↦ by
    simp [(hl.mem_erase_iff.1 hx).1]

lemma mem_bfsList (hl : ∀ w, w ∈ l) : v ∈ G.bfsList u l ↔ G.Reachable u v := by
  refine ⟨reachable_of_mem_bfsIterate (fun x hx ↦ hx) (fun x hx ↦ ?_), fun hv ↦ ?_⟩
  · rw [List.mem_singleton] at hx
    exact hx ▸ .refl _
  · refine mem_bfsIterate_of_reachable (by simp [hl]) (by simp) (fun x ↦ ?_) (by simp) hv
    obtain rfl | hxu := eq_or_ne x u
    · exact .inr (by simp)
    · exact .inl <| (List.mem_erase_of_ne hxu).2 <| hl x

lemma preconnected_iff_forall_mem_bfsList (hl : ∀ w, w ∈ l) (u : V) :
    G.Preconnected ↔ ∀ v, v ∈ G.bfsList u l := by
  simp only [mem_bfsList hl]
  exact ⟨fun h v ↦ h u v, fun h x y ↦ (h x).symm.trans (h y)⟩

lemma connected_iff_forall_mem_bfsList (hl : ∀ w, w ∈ l) (u : V) :
    G.Connected ↔ ∀ v, v ∈ G.bfsList u l := by
  rw [connected_iff, preconnected_iff_forall_mem_bfsList hl u, and_iff_left ⟨u⟩]

/-- Breadth-first search from `u` visits every vertex iff it visits as many vertices as there are,
since it visits each vertex at most once.

Comparing lengths is faster than checking membership of every vertex, so this is the criterion used
by the `SimpleGraph.decidablePreconnected` and `SimpleGraph.decidableConnected` instances. -/
lemma length_bfsList_eq_iff (hl : l.Nodup) (hl' : ∀ w, w ∈ l) (u : V) :
    (G.bfsList u l).length = l.length ↔ ∀ v, v ∈ G.bfsList u l := by
  have hsub : List.Subperm (G.bfsList u l) l :=
    (nodup_bfsList hl).subperm fun _ hv ↦ mem_of_mem_bfsList (hl' u) hv
  exact ⟨fun h v ↦ (hsub.perm_of_length_le h.ge).mem_iff.2 (hl' v), fun h ↦
    le_antisymm hsub.length_le (hl.subperm fun v _ ↦ h v).length_le⟩

lemma preconnected_iff_length_bfsList (hl : l.Nodup) (hl' : ∀ w, w ∈ l) (u : V) :
    G.Preconnected ↔ (G.bfsList u l).length = l.length := by
  rw [preconnected_iff_forall_mem_bfsList hl' u, length_bfsList_eq_iff hl hl']

lemma connected_iff_length_bfsList (hl : l.Nodup) (hl' : ∀ w, w ∈ l) (u : V) :
    G.Connected ↔ (G.bfsList u l).length = l.length := by
  rw [connected_iff_forall_mem_bfsList hl' u, length_bfsList_eq_iff hl hl']

variable [Fintype V]

/-- Decides reachability of vertices `u` and `v` by performing a breadth-first search from `u`. -/
instance decidableReachable : DecidableRel G.Reachable := fun _u _v ↦
  (Fintype.truncList V).lift (fun l ↦ decidable_of_iff _ (mem_bfsList l.2.2))
    fun _ _ ↦ Subsingleton.elim ..

/-- Decides preconnectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidablePreconnected : Decidable G.Preconnected :=
  (Fintype.truncList V).lift
    (fun ⟨l, hl⟩ ↦ match l, hl with
      | [], hl => isTrue fun x _ ↦ absurd (hl.2 x) (by simp)
      | u :: l, hl => decidable_of_iff _ (preconnected_iff_length_bfsList hl.1 hl.2 u).symm)
    fun _ _ ↦ Subsingleton.elim ..

/-- Decides connectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidableConnected : Decidable G.Connected :=
  (Fintype.truncList V).lift
    (fun ⟨l, hl⟩ ↦ match l, hl with
      | [], hl => isFalse fun hG ↦ absurd (hl.2 hG.nonempty.some) (by simp)
      | u :: l, hl => decidable_of_iff _ (connected_iff_length_bfsList hl.1 hl.2 u).symm)
    fun _ _ ↦ Subsingleton.elim ..

instance : Fintype G.ConnectedComponent :=
  fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn (fun w ↦ decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

end BFS

section Fintype

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G ≤ G')
    (c' : ConnectedComponent G') [Fintype c'.supp]
    [DecidablePred fun c : G.ConnectedComponent ↦ c.supp ⊆ c'.supp] :
    .disjiUnion {c : ConnectedComponent G | c.supp ⊆ c'.supp} (fun c ↦ c.supp.toFinset)
      (fun x _ y _ hxy ↦ by simpa using pairwise_disjoint_supp_connectedComponent _ hxy) =
      c'.supp.toFinset :=
  Finset.coe_injective <| by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

end Fintype

/-- The odd components are the connected components of odd cardinality. This definition excludes
infinite components. -/
abbrev oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}

set_option backward.isDefEq.respectTransparency.types false in
lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp [Finite V] {G'}
    (h : G ≤ G') (c' : ConnectedComponent G') :
    Odd {c ∈ G.oddComponents | c.supp ⊆ c'.supp}.ncard ↔ Odd c'.supp.ncard := by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp, ← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

lemma odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.card V) := by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent ↦ x.supp.ncard)).symm

lemma ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G ≤ G') :
     G'.oddComponents.ncard ≤ G.oddComponents.ncard := by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp ⊆ c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' ↦ Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp h).2 hc
  let f : G'.oddComponents → G.oddComponents :=
    fun ⟨c, hc⟩ ↦ ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' ↦ ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

end SimpleGraph
