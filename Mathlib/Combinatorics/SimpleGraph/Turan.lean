/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Partition.Equipartition

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem

## TODO

* Prove the reverse direction of Turán's theorem at
  https://github.com/leanprover-community/mathlib4/pull/9317
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
  {n r : ℕ}

section Defs

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

variable {G H}

lemma IsTuranMaximal.le_iff_eq (hG : G.IsTuranMaximal r) (hH : H.CliqueFree (r + 1)) :
    G ≤ H ↔ G = H := by
  classical exact ⟨fun hGH ↦ edgeFinset_inj.1 <| eq_of_subset_of_card_le
    (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 _ hH), le_of_eq⟩

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

instance turanGraph.instDecidableRelAdj : DecidableRel (turanGraph n r).Adj := by
  dsimp only [turanGraph]; infer_instance

@[simp]
lemma turanGraph_zero : turanGraph n 0 = ⊤ := by
  ext a b; simp_rw [turanGraph, top_adj, Nat.mod_zero, not_iff_not, Fin.val_inj]

@[simp]
theorem turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r := by
  simp_rw [SimpleGraph.ext_iff, Function.funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.trans_le h), Nat.mod_eq_of_lt (b.2.trans_le h), Fin.val_inj]

variable (hr : 0 < r)

theorem turanGraph_cliqueFree : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra h
  rw [not_isEmpty_iff] at h
  obtain ⟨f, ha⟩ := h
  simp only [turanGraph, top_adj] at ha
  obtain ⟨x, y, d, c⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun x ↦
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  simp only [Fin.mk.injEq] at c
  exact absurd c ((@ha x y).mpr d)

/-- For `n ≤ r` and `0 < r`, `turanGraph n r` is Turán-maximal. -/
theorem isTuranMaximal_turanGraph (h : n ≤ r) : (turanGraph n r).IsTuranMaximal r :=
  ⟨turanGraph_cliqueFree hr, fun _ _ _ ↦
    card_le_card (edgeFinset_mono ((turanGraph_eq_top.mpr (Or.inr h)).symm ▸ le_top))⟩

/-- An `r + 1`-cliquefree Turán-maximal graph is _not_ `r`-cliquefree
if it can accommodate such a clique. -/
theorem not_cliqueFree_of_isTuranMaximal (hn : r ≤ Fintype.card V) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_smaller_set (univ : Finset V) r hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
  exact hGab <| le_sup_right.trans_eq ((hG.le_iff_eq <| h.sup_edge _ _).1 le_sup_left).symm <|
    (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

lemma exists_isTuranMaximal :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H.IsTuranMaximal r := by
  classical
  let c := {H : SimpleGraph V | H.CliqueFree (r + 1)}
  have cn : c.toFinset.Nonempty := ⟨⊥, by
    simp only [Set.toFinset_setOf, mem_filter, mem_univ, true_and, c]
    exact cliqueFree_bot (by omega)⟩
  obtain ⟨S, Sm, Sl⟩ := exists_max_image c.toFinset (·.edgeFinset.card) cn
  use S, inferInstance
  rw [Set.mem_toFinset] at Sm
  refine ⟨Sm, ?_⟩
  intro I _ cf
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

section Forward

variable {G}
variable {s t u : V} (h : G.IsTuranMaximal r)

namespace IsTuranMaximal

/-- In a Turán-maximal graph, non-adjacent vertices have the same degree. -/
lemma degree_eq_of_not_adj (hn : ¬G.Adj s t) : G.degree s = G.degree t := by
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_lt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  use G.replaceVertex s t, inferInstance, cf.replaceVertex s t
  have := G.card_edgeFinset_replaceVertex_of_not_adj hn
  omega

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
lemma not_adj_trans (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) : ¬G.Adj t u := by
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t).replaceVertex s u
  have nst : s ≠ t := fun a ↦ hsu (a ▸ h)
  have ntu : t ≠ u := G.ne_of_adj h
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, dst, Nat.add_sub_cancel]
  have l1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t
    · simpa only [eq, not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have l2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    rw [degree, degree, ← card_singleton t, ← card_sdiff (by simp [h.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs <;> simp_all [adj_comm]
  have l3 : 0 < G.degree u := by rw [G.degree_pos_iff_exists_adj u]; use t, h.symm
  omega

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem equivalence_not_adj : Equivalence fun x y ↦ ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact h.not_adj_trans xy yz

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩

instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

/-- The finpartition derived from `h.setoid`. -/
def finpartition : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

lemma not_adj_iff_part_eq : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t ∈ fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s), eq_comm]

lemma degree_eq_card_sub_part_card : G.degree s = Fintype.card V - (h.finpartition.part s).card :=
  calc
    _ = (univ.filter fun b ↦ G.Adj s b).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter fun b ↦ ¬G.Adj s b).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert Finpartition.mem_part_ofSetoid_iff_rel.symm
      simp [setoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem isEquipartition : h.finpartition.IsEquipartition := by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  apply absurd h
  rw [IsTuranMaximal]; push_neg; intro cf
  use G.replaceVertex v w, inferInstance, cf.replaceVertex v w
  have large_eq := fp.part_eq_of_mem hl hw
  have small_eq := fp.part_eq_of_mem hs hv
  have ha : G.Adj v w := by
    by_contra hn; rw [h.not_adj_iff_part_eq, small_eq, large_eq] at hn
    rw [hn] at ineq; omega
  rw [G.card_edgeFinset_replaceVertex_of_adj ha,
    degree_eq_card_sub_part_card h, small_eq, degree_eq_card_sub_part_card h, large_eq]
  have : large.card ≤ Fintype.card V := by simpa using card_le_card large.subset_univ
  omega

lemma card_parts_le : h.finpartition.parts.card ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree z.card := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose! hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (h.1.mono (Nat.succ_le_of_lt l)) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
`min` handles the `n < r` case, when `G` is complete but still `r + 1`-cliquefree
for having insufficiently many vertices. -/
theorem card_parts : h.finpartition.parts.card = min (Fintype.card V) r := by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ ↦ fp.part_mem (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; push_neg; rintro -
  have cf : G.CliqueFree r := by
    simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
      forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff, Set.Pairwise]
    intro z zc; push_neg; simp_rw [h.not_adj_iff_part_eq]
    exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ ↦ fp.part_mem (mem_univ a)
  use G ⊔ edge x y, inferInstance, cf.sup_edge x y
  convert Nat.lt.base G.edgeFinset.card
  convert G.card_edgeFinset_sup_edge _ hn
  rwa [h.not_adj_iff_part_eq]

/-- **Turán's theorem**, forward direction.

Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
theorem nonempty_iso_turanGraph : Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_eq] at this
  rw [← not_iff_not, not_ne_iff, this, card_parts]
  rcases le_or_lt r (Fintype.card V) with c | c
  · rw [min_eq_right c]; rfl
  · have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le, Nat.mod_eq_of_lt (lc a), Nat.mod_eq_of_lt (lc b),
      ← Nat.mod_eq_of_lt ((lc a).trans c), ← Nat.mod_eq_of_lt ((lc b).trans c)]; rfl

end IsTuranMaximal

end Forward

end SimpleGraph
