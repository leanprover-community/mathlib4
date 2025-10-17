/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : ℕ}

variable (G) in
/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → #H.edgeFinset ≤ #G.edgeFinset

section Defs

variable {H : SimpleGraph V}

lemma IsTuranMaximal.le_iff_eq (hG : G.IsTuranMaximal r) (hH : H.CliqueFree (r + 1)) :
    G ≤ H ↔ G = H := by
  classical exact ⟨fun hGH ↦ edgeFinset_inj.1 <| eq_of_subset_of_card_le
    (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 _ hH), le_of_eq⟩

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

lemma turanGraph_adj {v w} : (turanGraph n r).Adj v w ↔ v % r ≠ w % r :=
  .rfl

instance turanGraph.instDecidableRelAdj : DecidableRel (turanGraph n r).Adj := by
  dsimp only [turanGraph]; infer_instance

@[simp]
lemma turanGraph_zero : turanGraph n 0 = ⊤ := by
  ext a b; simp_rw [turanGraph, top_adj, Nat.mod_zero, not_iff_not, Fin.val_inj]

@[simp]
theorem turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r := by
  simp_rw [SimpleGraph.ext_iff, funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.trans_le h), Nat.mod_eq_of_lt (b.2.trans_le h), Fin.val_inj]

theorem turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra! h
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
  obtain ⟨K, _, rfl⟩ := exists_subset_card_eq hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
  exact hGab <| le_sup_right.trans_eq ((hG.le_iff_eq <| h.sup_edge _ _).1 le_sup_left).symm <|
    (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

lemma exists_isTuranMaximal (hr : 0 < r) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H.IsTuranMaximal r := by
  classical
  let c := {H : SimpleGraph V | H.CliqueFree (r + 1)}
  have cn : c.toFinset.Nonempty := ⟨⊥, by
    rw [Set.toFinset_setOf, mem_filter_univ]
    exact cliqueFree_bot (by cutsat)⟩
  obtain ⟨S, Sm, Sl⟩ := exists_max_image c.toFinset (#·.edgeFinset) cn
  use S, inferInstance
  rw [Set.mem_toFinset] at Sm
  refine ⟨Sm, fun I _ cf ↦ ?_⟩
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

namespace IsTuranMaximal

variable {s t u : V}

/-- In a Turán-maximal graph, non-adjacent vertices have the same degree. -/
lemma degree_eq_of_not_adj (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t) :
    G.degree s = G.degree t := by
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_gt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  classical
  use G.replaceVertex s t, inferInstance, cf.replaceVertex s t
  have := G.card_edgeFinset_replaceVertex_of_not_adj hn
  cutsat

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
lemma not_adj_trans (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u) :
    ¬G.Adj t u := by
  have hst : ¬G.Adj s t := fun a ↦ hts a.symm
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal] at h; contrapose! h; intro cf
  classical
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t).replaceVertex s u
  have nst : s ≠ t := fun a ↦ hsu (a ▸ h)
  have ntu : t ≠ u := G.ne_of_adj h
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, dst, Nat.add_sub_cancel]
  have l1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset]
    by_cases eq : v = t
    · simpa only [eq, not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have l2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    rw [degree, degree, ← card_singleton t, ← card_sdiff_of_subset (by simp [h.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs <;> simp_all [adj_comm]
  have l3 : 0 < G.degree u := by rw [G.degree_pos_iff_exists_adj u]; use t, h.symm
  cutsat

variable (h : G.IsTuranMaximal r)
include h

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
def finpartition [DecidableEq V] : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

lemma not_adj_iff_part_eq [DecidableEq V] :
    ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t ∈ fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s), eq_comm]

lemma degree_eq_card_sub_part_card [DecidableEq V] :
    G.degree s = Fintype.card V - #(h.finpartition.part s) :=
  calc
    _ = #{t | G.Adj s t} := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - #{t | ¬G.Adj s t} :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert Finpartition.mem_part_ofSetoid_iff_rel.symm
      simp [setoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem isEquipartition [DecidableEq V] : h.finpartition.IsEquipartition := by
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
  have : #large ≤ Fintype.card V := by simpa using card_le_card large.subset_univ
  cutsat

lemma card_parts_le [DecidableEq V] : #h.finpartition.parts ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose! hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (h.1.mono (Nat.succ_le_of_lt l)) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
`min` handles the `n < r` case, when `G` is complete but still `r + 1`-cliquefree
for having insufficiently many vertices. -/
theorem card_parts [DecidableEq V] : #h.finpartition.parts = min (Fintype.card V) r := by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ ↦ fp.part_mem.2 (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; push_neg; rintro -
  have cf : G.CliqueFree r := by
    simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
      forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff, Set.Pairwise]
    intro z zc; push_neg; simp_rw [h.not_adj_iff_part_eq]
    exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ ↦
      fp.part_mem.2 (mem_univ a)
  use G ⊔ edge x y, inferInstance, cf.sup_edge x y
  convert Nat.lt.base #G.edgeFinset
  convert G.card_edgeFinset_sup_edge _ hn
  rwa [h.not_adj_iff_part_eq]

/-- **Turán's theorem**, forward direction.

Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
theorem nonempty_iso_turanGraph :
    Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
  classical
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_eq] at this
  rw [← not_iff_not, not_ne_iff, this, card_parts]
  rcases le_or_gt r (Fintype.card V) with c | c
  · rw [min_eq_right c]; rfl
  · have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le, Nat.mod_eq_of_lt (lc a), Nat.mod_eq_of_lt (lc b),
      ← Nat.mod_eq_of_lt ((lc a).trans c), ← Nat.mod_eq_of_lt ((lc b).trans c)]; rfl

end IsTuranMaximal

/-- **Turán's theorem**, reverse direction.

Any graph isomorphic to `turanGraph n r` is itself Turán-maximal if `0 < r`. -/
theorem isTuranMaximal_of_iso (f : G ≃g turanGraph n r) (hr : 0 < r) : G.IsTuranMaximal r := by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq, Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f,
    fun H _ cf ↦ (f.symm.comp g).card_edgeFinset_eq ▸ j.2 H cf

/-- Turán-maximality with `0 < r` transfers across graph isomorphisms. -/
theorem IsTuranMaximal.iso {W : Type*} [Fintype W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (h : G.IsTuranMaximal r) (f : G ≃g H) (hr : 0 < r) : H.IsTuranMaximal r :=
  isTuranMaximal_of_iso (h.nonempty_iso_turanGraph.some.comp f.symm) hr

/-- For `0 < r`, `turanGraph n r` is Turán-maximal. -/
theorem isTuranMaximal_turanGraph (hr : 0 < r) : (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_of_iso Iso.refl hr

/-- **Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices. -/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r) :=
  ⟨fun h ↦ h.nonempty_iso_turanGraph, fun h ↦ isTuranMaximal_of_iso h.some hr⟩

/-! ### Number of edges in the Turán graph -/

private lemma sum_ne_add_mod_eq_sub_one {c : ℕ} :
    ∑ w ∈ range r, (if c % r ≠ (n + w) % r then 1 else 0) = r - 1 := by
  rcases r.eq_zero_or_pos with rfl | hr; · simp
  suffices #{i ∈ range r | c % r = (n + i) % r} = 1 by
    rw [← card_filter, ← this]; apply Nat.eq_sub_of_add_eq'
    rw [filter_card_add_filter_neg_card_eq_card, card_range]
  apply le_antisymm
  · change #{i ∈ range r | _ ≡ _ [MOD r]} ≤ 1
    rw [card_le_one_iff]; intro w x mw mx
    simp only [mem_filter, mem_range] at mw mx
    have := mw.2.symm.trans mx.2
    rw [Nat.ModEq.add_iff_left rfl] at this
    change w % r = x % r at this
    rwa [Nat.mod_eq_of_lt mw.1, Nat.mod_eq_of_lt mx.1] at this
  · rw [one_le_card]; use ((r - 1) * n + c) % r
    simp only [mem_filter, mem_range]; refine ⟨Nat.mod_lt _ hr, ?_⟩
    rw [Nat.add_mod_mod, ← add_assoc, ← one_add_mul, show 1 + (r - 1) = r by cutsat,
      Nat.mul_add_mod_self_left]

lemma card_edgeFinset_turanGraph_add :
    #(turanGraph (n + r) r).edgeFinset =
    #(turanGraph n r).edgeFinset + n * (r - 1) + r.choose 2 := by
  rw [← mul_right_inj' two_ne_zero]
  simp_rw [mul_add, ← sum_degrees_eq_twice_card_edges,
    degree, neighborFinset_eq_filter, turanGraph, card_filter]
  conv_lhs =>
    enter [2, v]
    rw [Fin.sum_univ_eq_sum_range fun w ↦ if v % r ≠ w % r then 1 else 0, sum_range_add]
  rw [sum_add_distrib,
    Fin.sum_univ_eq_sum_range fun v ↦ ∑ w ∈ range n, if v % r ≠ w % r then 1 else 0,
    Fin.sum_univ_eq_sum_range fun v ↦ ∑ w ∈ range r, if v % r ≠ (n + w) % r then 1 else 0,
    sum_range_add, sum_range_add, add_assoc, add_assoc]
  congr 1; · simp [← Fin.sum_univ_eq_sum_range]
  rw [← add_assoc, sum_comm]; simp_rw [ne_comm, ← two_mul]; congr
  · conv_rhs => rw [← card_range n, ← smul_eq_mul, ← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one
  · rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
    conv_rhs => enter [1]; rw [← card_range r]
    rw [← smul_eq_mul, ← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one

/-- The exact formula for the number of edges in `turanGraph n r`. -/
theorem card_edgeFinset_turanGraph {n r : ℕ} :
    #(turanGraph n r).edgeFinset =
    (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [Nat.mod_zero, tsub_self, zero_mul, Nat.zero_div, zero_add]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at this; convert this; exact turanGraph_zero
  · have ring₁ (n) : (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) =
        n % r * (n / r) * (r - 1) + r * (r - 1) * (n / r) ^ 2 / 2 := by
      nth_rw 1 [← Nat.mod_add_div n r, Nat.sq_sub_sq, add_tsub_cancel_left,
        show (n % r + r * (n / r) + n % r) * (r * (n / r)) * (r - 1) =
          (2 * ((n % r) * (n / r) * (r - 1)) + r * (r - 1) * (n / r) ^ 2) * r by grind]
      rw [Nat.mul_div_mul_right _ _ hr, Nat.mul_add_div zero_lt_two]
    rcases lt_or_ge n r with h | h
    · rw [Nat.mod_eq_of_lt h, tsub_self, zero_mul, Nat.zero_div, zero_add]
      have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
      rw [Fintype.card_fin] at this; convert this
      rw [turanGraph_eq_top]; exact .inr h.le
    · let n' := n - r
      have n'r : n = n' + r := by omega
      rw [n'r, card_edgeFinset_turanGraph_add, card_edgeFinset_turanGraph, ring₁, ring₁,
        add_rotate, ← add_assoc, Nat.add_mod_right, Nat.add_div_right _ hr]
      congr 1
      have rd : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self _).two_dvd
      rw [← Nat.div_mul_right_comm rd, ← Nat.div_mul_right_comm rd, ← Nat.choose_two_right]
      have ring₂ : n' % r * (n' / r + 1) * (r - 1) + r.choose 2 * (n' / r + 1) ^ 2 =
          n' % r * (n' / r + 1) * (r - 1) + r.choose 2 +
          r.choose 2 * 2 * (n' / r) + r.choose 2 * (n' / r) ^ 2 := by grind
      rw [ring₂, ← add_assoc]; congr 1
      rw [← add_rotate, ← add_rotate _ _ (r.choose 2)]; congr 1
      rw [Nat.choose_two_right, Nat.div_mul_cancel rd, mul_add_one, add_mul, ← add_assoc,
        ← add_rotate, add_comm _ (_ *_)]; congr 1
      rw [← mul_rotate, ← add_mul, add_comm, mul_comm _ r, Nat.div_add_mod n' r]

/-- A looser (but simpler than `card_edgeFinset_turanGraph`) bound on the number of edges in
`turanGraph n r`. -/
theorem mul_card_edgeFinset_turanGraph_le :
    2 * r * #(turanGraph n r).edgeFinset ≤ (r - 1) * n ^ 2 := by
  grw [card_edgeFinset_turanGraph, mul_add, Nat.mul_div_le]
  rw [tsub_mul, ← Nat.sub_add_comm]; swap
  · grw [Nat.mod_le]
    exact Nat.zero_le _
  rw [Nat.sub_le_iff_le_add, mul_comm, Nat.add_le_add_iff_left, Nat.choose_two_right,
    ← Nat.mul_div_assoc _ (Nat.even_mul_pred_self _).two_dvd, mul_assoc,
    mul_div_cancel_left₀ _ two_ne_zero, ← mul_assoc, ← mul_rotate, sq, ← mul_rotate (r - 1)]
  gcongr ?_ * _
  rcases r.eq_zero_or_pos with rfl | hr; · cutsat
  rw [Nat.sub_one_mul, Nat.sub_one_mul, mul_comm]
  exact Nat.sub_le_sub_left (Nat.mod_lt _ hr).le _

theorem CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
    let n := Fintype.card V;
    #G.edgeFinset ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [cliqueFree_one, ← Fintype.card_eq_zero_iff] at cf
    simp_rw [zero_tsub, mul_zero, Nat.mod_zero, Nat.div_zero, zero_add]
    exact card_edgeFinset_le_card_choose_two
  · obtain ⟨H, _, maxH⟩ := exists_isTuranMaximal (V := V) hr
    convert maxH.2 _ cf
    rw [((isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH).some.card_edgeFinset_eq,
      card_edgeFinset_turanGraph]

end SimpleGraph
