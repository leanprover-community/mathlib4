/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Partition.Equipartition
import Mathlib.Tactic.Zify

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

For the reverse direction we first show that a Turán-maximal graph exists, then transfer
the property through `turanGraph n r` using the isomorphism provided by the forward direction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n r : ℕ}

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

variable {G} {H : SimpleGraph V}

section Defs

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
  refine ⟨Sm, fun I _ cf ↦ ?_⟩
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

namespace IsTuranMaximal

variable {s t u : V} (h : G.IsTuranMaximal r)

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
lemma not_adj_trans (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u) : ¬G.Adj t u := by
  have hst : ¬G.Adj s t := fun a ↦ hts a.symm
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
theorem equivalence_not_adj : Equivalence (¬G.Adj · ·) where
  refl := by simp
  symm := by simp [adj_comm]
  trans := h.not_adj_trans

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩

instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel (¬G.Adj · ·)

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
    _ = (univ.filter (G.Adj s)).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter (¬G.Adj s ·)).card :=
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

variable (hr : 0 < r)

/-- **Turán's theorem**, reverse direction.

Any graph isomorphic to `turanGraph n r` is itself Turán-maximal. -/
theorem isTuranMaximal_of_iso (f : G ≃g turanGraph n r) : G.IsTuranMaximal r := by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq, Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f,
    fun H _ cf ↦ (f.symm.comp g).card_edgeFinset_eq ▸ j.2 H cf

/-- For `0 < r`, `turanGraph n r` is Turán-maximal. -/
theorem isTuranMaximal_turanGraph : (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_of_iso hr Iso.refl

/-- **Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices. -/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r) :=
  ⟨fun h ↦ h.nonempty_iso_turanGraph, fun h ↦ isTuranMaximal_of_iso hr h.some⟩

/-- Recurrence for the number of edges in the Turán graph. -/
theorem card_edgeFinset_turanGraph_add (hr : 0 < r) : (turanGraph (n + r) r).edgeFinset.card =
    (turanGraph n r).edgeFinset.card + r.choose 2 + (r - 1) * n := by
  -- We split the graph's edges into three parts.
  rw [← filter_univ_mem (turanGraph (n + r) r).edgeFinset,
    ← filter_card_add_filter_neg_card_eq_card (fun e ↦ ∀ x : Fin (n + r), x ∈ e → x < n),
    filter_filter, filter_filter, add_assoc]
  congr 1
  · -- Edges in the first part have both endpoints `< n`.
    -- They are exactly the edges in `turanGraph n r`.
    let f : Sym2 (Fin n) ↪ Sym2 (Fin (n + r)) := ⟨_, Sym2.map.injective (Fin.castAdd_injective n r)⟩
    rw [← filter_univ_mem (turanGraph n r).edgeFinset, ← card_map f]
    congr; ext e; refine e.inductionOn fun ⟨x, _⟩ ⟨y, _⟩ ↦ ?_
    simp_rw [mem_map, mem_filter, mem_univ, true_and, mem_edgeFinset, turanGraph, Sym2.exists,
      Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_edgeSet, f, Function.Embedding.coeFn_mk,
      Sym2.map_pair_eq, Sym2.eq_iff, Fin.castAdd, Fin.castLE, Fin.mk.injEq]
    refine ⟨fun ⟨q, lx, ly⟩ ↦ ?_, fun ⟨⟨_, _⟩, ⟨_, _⟩, _, h⟩ ↦ ?_⟩
    · use ⟨x, lx⟩, ⟨y, ly⟩, q; tauto
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  rw [← filter_card_add_filter_neg_card_eq_card (fun e ↦ ∀ x : Fin (n + r), x ∈ e → n ≤ x),
    filter_filter, filter_filter]
  congr
  · -- Edges in the second part have both endpoints `≥ n`. They span `r` consecutive numbers;
    -- since adjacency in `TuranGraph` is defined by modular inequality modulo `r`,
    -- every possible edge must be included, so there are `r.choose 2` edges in this part.
    have ceq := Sym2.card_image_offDiag (univ : Finset (Fin r))
    rw [card_univ, Fintype.card_fin] at ceq
    let f : Sym2 (Fin r) ↪ Sym2 (Fin (n + r)) :=
      ⟨Sym2.map (Fin.natAdd n), Sym2.map.injective (fun _ _ ↦ by simp [Fin.ext_iff])⟩
    rw [← ceq, ← card_map f]
    congr; ext e; refine e.inductionOn fun ⟨x, lx⟩ ⟨y, ly⟩ ↦ ?_
    simp_rw [mem_map, mem_filter, mem_image, mem_offDiag, mem_univ, true_and, mem_edgeFinset,
      turanGraph, Sym2.exists, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp, forall_eq, f, and_assoc,
      show ¬(x < n ∧ y < n) ∧ n ≤ x ∧ n ≤ y ↔ n ≤ x ∧ n ≤ y by omega, Function.Embedding.coeFn_mk,
      Sym2.map_pair_eq, Fin.natAdd, Sym2.eq_iff, Fin.mk.injEq, Prod.exists, Sym2.eq_iff]
    refine ⟨fun ⟨q, gx, gy⟩ ↦ ?_, fun h ↦ ?_⟩
    · have mx := Nat.mod_eq_of_lt (Nat.sub_lt_left_of_lt_add gx lx)
      have my := Nat.mod_eq_of_lt (Nat.sub_lt_left_of_lt_add gy ly)
      use ⟨_, (x - n).mod_lt hr⟩, ⟨_, (y - n).mod_lt hr⟩; constructor
      · use ⟨_, (x - n).mod_lt hr⟩, ⟨_, (y - n).mod_lt hr⟩
        simp only [ne_eq, Fin.mk.injEq, true_or, and_true, mx, my]
        contrapose! q; rw [show x = y by omega]
      · simp_rw [mx, my]; omega
    · obtain ⟨⟨x₁, lx₁⟩, ⟨y₁, ly₁⟩, ⟨⟨x₂, lx₂⟩, ⟨y₂, ly₂⟩, c₂, c₃⟩, c₁⟩ := h
      simp only [ne_eq, Fin.mk.injEq] at c₁ c₂ c₃
      refine ⟨?_, by omega, by omega⟩
      rcases c₁ with c | c <;> rw [← c.1, ← c.2] <;> rcases c₃ with d | d <;> rw [← d.1, ← d.2]
      all_goals
        rw [ne_eq]; zify; rw [Int.emod_add_cancel_left]; norm_cast
        rw [Nat.mod_eq_of_lt lx₂, Nat.mod_eq_of_lt ly₂]; tauto
  · -- The remaining edges join a number `< n` with one `≥ n`. A vertex `x < n` is connected to
    -- all `r` vertices `≥ n` except `n + (x - n) % r`, thus `r - 1` vertices, and there are
    -- a total of `(r - 1) * n` edges in this part.
    let g : Fin n → Finset (Fin n × Fin r) :=
      fun x ↦ {x} ×ˢ (univ \ {⟨_, (x + (r - 1) * n).mod_lt hr⟩})
    have gc : ∀ x, (g x).card = r - 1 := fun x ↦ by
      simp_rw [g, card_product, card_singleton, one_mul, card_univ_diff, card_singleton,
        Fintype.card_fin]
    have gd : (univ.biUnion g).card = (r - 1) * n := by
      rw [card_biUnion]
      simp_rw [gc, sum_const, Nat.nsmul_eq_mul, card_univ, Fintype.card_fin, mul_comm]
      intros; simp_rw [g, disjoint_product, disjoint_singleton_left, mem_singleton]; tauto
    let f : Fin n × Fin r ↪ Sym2 (Fin (n + r)) :=
      ⟨fun p ↦ s(Fin.castAdd r p.1, Fin.natAdd n p.2), fun ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ ↦ by
        simp_rw [Fin.castAdd, Fin.castLE, Fin.natAdd, Sym2.eq_iff, Fin.mk.injEq, Prod.mk.injEq]
        omega⟩
    rw [← gd, ← card_map f]
    congr; ext e; refine e.inductionOn fun ⟨x, lx⟩ ⟨y, ly⟩ ↦ ?_
    simp_rw [mem_map, mem_biUnion, mem_filter, mem_univ, true_and, mem_edgeFinset, turanGraph,
      mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp, forall_eq, f, and_assoc, Prod.exists,
      Fin.castAdd, Fin.castLE, Fin.natAdd, Function.Embedding.coeFn_mk, Sym2.eq_iff, Fin.mk.injEq]
    simp_rw [g, singleton_product, mem_map, mem_sdiff, mem_univ, true_and, mem_singleton,
      Function.Embedding.coeFn_mk, Prod.mk.injEq, exists_eq_right_right, exists_eq_right,
      show ¬(x < n ∧ y < n) ∧ ¬(n ≤ x ∧ n ≤ y) ↔ (x < n ∧ n ≤ y) ∨ (y < n ∧ n ≤ x) by omega]
    refine ⟨fun ⟨q, c⟩ ↦ ?_, fun h ↦ ?_⟩
    · rcases c with ⟨cx, cy⟩ | ⟨cy, cx⟩
      · refine ⟨⟨x, cx⟩, ⟨y - n, by omega⟩, ?_, by dsimp only; omega⟩
        simp_rw [Fin.mk.injEq]; rw [← Nat.mod_eq_of_lt (show y - n < r by omega)]; zify [hr, cy]
        rw [sub_one_mul, add_sub_assoc', Int.emod_sub_cancel_right, Int.add_mul_emod_self_left]
        exact_mod_cast q.symm
      · refine ⟨⟨y, cy⟩, ⟨x - n, by omega⟩, ?_, by dsimp only; omega⟩
        simp_rw [Fin.mk.injEq]; rw [← Nat.mod_eq_of_lt (show x - n < r by omega)]; zify [hr, cx]
        rw [sub_one_mul, add_sub_assoc', Int.emod_sub_cancel_right, Int.add_mul_emod_self_left]
        exact_mod_cast q
    · obtain ⟨⟨x', lx'⟩, ⟨y', ly'⟩, q, c⟩ := h; refine ⟨?_, by omega⟩
      simp only [Fin.mk.injEq] at q c; contrapose! q
      replace q : x' % r = (n + y') % r := by rcases c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [q]
      rw [← Nat.mod_eq_of_lt ly']; zify [hr]
      rw [sub_one_mul, add_sub_assoc', ← Int.add_sub_cancel y' n, Int.emod_sub_cancel_right,
        Int.add_mul_emod_self_left, add_comm]
      exact_mod_cast q.symm

end SimpleGraph
