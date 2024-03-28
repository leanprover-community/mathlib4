/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Order.Partition.Equipartition

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations show
that the graph is (isomorphic to) the Turán graph for the given parameters.

The reverse direction proceeds as in Turán's original proof, via induction on the vertex count.
If we know that `turanGraph n r` is Turán-maximal, consider any `r + 1`-cliquefree graph on
`n + r` vertices; we can assume without loss of generality that it is Turán-maximal. Maximality
implies there is an `r`-clique `K`, so the graph's edges split into three sets:
* Edges entirely within `K`, which number at most `r.choose 2`
* Edges entirely outside `K` and hence in the `n`-vertex subgraph induced by `Kᶜ`,
  which by the inductive hypothesis number at most `(turanGraph n r).edgeFinset.card`
* Edges spanning `K` and `Kᶜ`; no vertex in `Kᶜ` can connect to all of `K`, so this set of edges
  numbers at most `(r - 1) * n`
These bounds add up to exactly `(turanGraph (n + r) r).edgeFinset.card`, completing the induction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `isTuranMaximalIsoTuranGraph`: the forward direction, an isomorphism between `G` satisfying
  `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.
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
  refine' ⟨fun h ↦ _, _⟩
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

open Classical in
lemma exists_IsTuranMaximal : ∃ H : SimpleGraph V, H.IsTuranMaximal r := by
  let c := {H : SimpleGraph V | H.CliqueFree (r + 1)}
  have cn : c.toFinset.Nonempty := ⟨⊥, by
    simp only [Set.toFinset_setOf, mem_filter, mem_univ, true_and, c]
    exact cliqueFree_bot (by omega)⟩
  obtain ⟨S, Sm, Sl⟩ := exists_max_image c.toFinset (·.edgeFinset.card) cn
  use S
  rw [Set.mem_toFinset] at Sm
  refine' ⟨Sm, _⟩
  intro I _ cf
  by_cases Im : I ∈ c.toFinset
  · convert Sl I Im
  · rw [Set.mem_toFinset] at Im
    contradiction

end Defs

section EdgeCard

variable (hr : 0 < r)

/-- Equivalence 0 -/
def equivFin0 (p : ℕ → Prop) : { x : Fin n // p ↑x } ≃ { x : ℕ // x < n ∧ p x } where
  toFun := fun ⟨v, q⟩ ↦ ⟨v.1, ⟨v.2, q⟩⟩
  invFun := fun ⟨v, q⟩ ↦ ⟨⟨v, q.1⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem degree_turanGraph (v : Fin n) :
    (turanGraph n r).degree v = n - (n / r + if v % r < n % r then 1 else 0) := by
  simp_rw [← card_neighborFinset_eq_degree, neighborFinset, Set.toFinset_card,
    Fintype.card_ofFinset, mem_neighborSet, turanGraph, filter_not, card_univ_diff,
    Fintype.card_fin, ← Fintype.card_subtype]
  congr
  rw [← Nat.count_modEq_card _ hr, Nat.count_eq_card_fintype]
  apply @Fintype.card_congr _ _ _ (Nat.CountSet.fintype _ n) _
  convert (equivFin0 _) using 3
  rw [Nat.ModEq.comm]; rfl

private lemma aux2 : n - n / r = (r - 1) * (n / r) + n % r := by
  nth_rw 1 [← Nat.div_add_mod n r, add_comm]
  nth_rw 2 [← one_mul (n / r)]
  nth_rw 1 [add_tsub_assoc_of_le (by exact Nat.mul_le_mul_right (n / r) hr),
    ← tsub_mul, add_comm]

private lemma aux3 (v : ℕ) : n - (n / r + if v % r < n % r then 1 else 0) =
    (r - 1) * (n / r) + (n % r - if v % r < n % r then 1 else 0) := by
  rw [← Nat.sub_sub, aux2 hr, add_tsub_assoc_of_le]
  split_ifs with c
  · exact (zero_le _).trans_lt c
  · apply zero_le

private lemma aux4 : Even ((n + n % r) * (r - 1) * (n / r)) := by
  cases' (r - 1).even_or_odd with re ro
  · simp [re]
  · rw [Nat.odd_sub' hr] at ro
    simp only [Nat.odd_iff_not_even, Nat.not_even_one, not_false_eq_true, true_iff] at ro
    cases' n.even_or_odd with ne no
    · have v : Even (n + n % r) := Even.add ne ((Even.mod_even_iff ro).mpr ne)
      simp [v, parity_simps]
    · have v : Even (n + n % r) := Odd.add_odd no ((Odd.mod_even_iff ro).mpr no)
      simp [v, parity_simps]

open BigOperators

/-- Formula for the number of edges in `turanGraph n r`. -/
theorem card_edgeFinset_turanGraph : (turanGraph n r).edgeFinset.card =
    (n + n % r) * (r - 1) * (n / r) / 2 + (n % r).choose 2 := by
  rw [← mul_left_cancel_iff_of_pos zero_lt_two, ← sum_degrees_eq_twice_card_edges]
  simp_rw [degree_turanGraph hr, aux3 hr]
  rw [sum_add_distrib, sum_tsub_distrib]
  swap
  · intro x _
    split_ifs with c
    · exact (zero_le _).trans_lt c
    · apply zero_le
  simp_rw [sum_const, card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ if x % r < n % r then 1 else 0),
    ← sum_fiberwise_of_maps_to (g := (· % r)) (t := Ico 0 r) (fun _ _ ↦ by simp [Nat.mod_lt _ hr])]
  have : ∀ j ∈ Ico 0 r,
      (∑ i in (range n).filter (· % r = j), if i % r < n % r then 1 else 0) =
      if j < n % r then n.count (· ≡ j [MOD r]) else 0 := by
    intro j hj
    rw [sum_boole, filter_filter]
    split_ifs with hl
    · have re : (range n).filter (fun a ↦ a % r = j ∧ a % r < n % r) =
          (range n).filter (fun a ↦ a % r = j % r) := by
        ext a
        simp_rw [mem_filter, and_congr_right_iff]
        have je := Nat.mod_eq_of_lt (mem_Ico.mp hj).2
        intro; constructor
        · intro ⟨h1, _⟩; exact h1.trans je.symm
        · intro h; rw [h, je]; exact ⟨rfl, hl⟩
      rw [re, Nat.cast_id, Nat.count_eq_card_filter_range]; rfl
    · have re : (range n).filter (fun a ↦ a % r = j ∧ a % r < n % r) =
          (range n).filter (fun _ ↦ False) := by
        ext a
        simp_rw [mem_filter, and_congr_right_iff]
        intro; constructor
        · intro ⟨h1, h2⟩; exact absurd (h1 ▸ h2) hl
        · tauto
      simp [re]
  rw [sum_congr rfl this, ← sum_Ico_consecutive _ (Nat.zero_le _) (Nat.mod_lt n hr).le]
  clear this
  have : ∀ i ∈ Ico 0 (n % r),
      (if i < n % r then Nat.count (fun x ↦ x ≡ i [MOD r]) n else 0) = n / r + 1 := by
    intro i hi
    rw [mem_Ico] at hi
    simp_rw [hi.2, ite_true, Nat.count_modEq_card _ hr, (i.mod_le r).trans_lt hi.2, ite_true]
  rw [sum_congr rfl this, sum_const, Nat.Ico_zero_eq_range, card_range, smul_eq_mul]
  clear this
  have : ∀ i ∈ Ico (n % r) r,
      (if i < n % r then Nat.count (fun x ↦ x ≡ i [MOD r]) n else 0) = 0 := by
    intro i hi
    rw [mem_Ico] at hi
    simp [hi.1.not_lt]
  rw [sum_congr rfl this, sum_const_zero, add_zero]
  clear this
  rw [mul_comm n (n % r), ← Nat.mul_sub_left_distrib, ← Nat.sub_sub, mul_tsub, mul_one,
    ← add_tsub_assoc_of_le]
  swap
  · cases' (n % r).eq_zero_or_pos with h h; · simp [h]
    rw [le_mul_iff_one_le_right h, Nat.one_le_iff_ne_zero, Nat.sub_ne_zero_iff_lt]
    change 1 ≤ r at hr
    cases' hr.eq_or_gt with i i
    · rw [i, Nat.mod_one] at h; simp at h
    · refine' Nat.div_lt_self _ i
      contrapose! h
      simp only [nonpos_iff_eq_zero] at h; subst h; simp
  rw [aux2 hr, mul_add, ← add_assoc, ← add_mul, ← mul_assoc]
  rw [mul_add, Nat.two_mul_div_two_of_even (aux4 hr), add_tsub_assoc_of_le (Nat.le_mul_self _)]
  congr
  cases' (n % r).eq_zero_or_pos with h h; · simp [h]
  rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _), mul_tsub,
    mul_one]

theorem card_edgeFinset_turanGraph_add : (turanGraph (n + r) r).edgeFinset.card =
    r.choose 2 + (r - 1) * n + (turanGraph n r).edgeFinset.card := by
  simp_rw [card_edgeFinset_turanGraph hr, Nat.add_mod_right]
  rw [Nat.add_div_right _ hr, ← add_assoc]; congr
  rw [Nat.mul_succ]
  conv_lhs => enter [1, 1, 1, 1]; rw [add_assoc, add_comm r, ← add_assoc]
  rw [add_mul, add_mul, add_assoc]
  conv_lhs =>
    enter [1, 2]
    rw [mul_assoc, mul_comm, mul_comm _ (r - 1), mul_assoc, ← mul_add, mul_comm _ r,
      add_comm (n + r), ← add_assoc, Nat.div_add_mod, ← add_assoc, mul_comm, ← two_mul, add_mul]
  nth_rw 1 [← Nat.div_two_mul_two_of_even (aux4 hr),
    ← Nat.div_two_mul_two_of_even (n := 2 * n * (r - 1)) (by simp),
    ← Nat.div_two_mul_two_of_even (n := r * (r - 1)) (Nat.even_mul_pred_self _),
    ← add_mul, ← add_mul, Nat.mul_div_left _ zero_lt_two]
  rw [← Nat.choose_two_right, add_comm, add_comm _ (r.choose 2)]; congr
  rw [mul_assoc, mul_comm, Nat.mul_div_left _ zero_lt_two, mul_comm]

end EdgeCard

section Forward

variable {s t u : V} (hmax : G.IsTuranMaximal r)

/-- First part of Zykov symmetrisation. If vertex `s` has larger degree than
a non-adjacent other vertex `t`, `G.replaceVertex s t` has more edges than `G`. -/
theorem card_lt_card_replaceVertex1 (hn : ¬G.Adj s t) (hd : G.degree t < G.degree s) :
    G.edgeFinset.card < (G.replaceVertex s t).edgeFinset.card := by
  rw [G.card_edgeFinset_replaceVertex_of_not_adj hn, add_tsub_assoc_of_le hd.le]
  exact Nat.lt_add_of_pos_right <| tsub_pos_iff_lt.mpr hd

/-- Second part of Zykov symmetrisation. A witness to non-transitivity of non-adjacency
where the involved vertices have the same degree can be used to generate
(using `replaceVertex` only) a graph with more edges. -/
theorem card_lt_card_replaceVertex2 (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) (htu : G.Adj t u)
    (hdt : G.degree s = G.degree t) (hdu : G.degree s = G.degree u) :
    G.edgeFinset.card < ((G.replaceVertex s t).replaceVertex s u).edgeFinset.card := by
  have ntu : t ≠ u := G.ne_of_adj htu
  have nst : s ≠ t := fun a => by subst a; contradiction
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, hdt, Nat.add_sub_cancel]
  have de1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t
    · subst eq
      simpa only [not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have de2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    unfold degree
    rw [← card_singleton t, ← card_sdiff (by simp [htu.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs with hu hv hv
    · simp_all
    · simp_all
    · simp [adj_comm, hsu, hv]
    · simp [adj_comm, hsu, hv]
  have dpos : 0 < G.degree u := by
    rw [G.degree_pos_iff_exists_adj u]
    use t
    exact htu.symm
  have dmp : G.degree u - 1 + 1 = G.degree u := Nat.succ_pred_eq_of_pos dpos
  nth_rw 1 [de1, de2, hdu, ← dmp, add_tsub_assoc_of_le (by simp), add_tsub_cancel_left]
  linarith

variable {G}

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
theorem not_adj_transitive (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) : ¬G.Adj t u := by
  by_cases z : G.degree s = G.degree t ∧ G.degree s = G.degree u <;>
    (contrapose! hmax; unfold IsTuranMaximal; push_neg; intro cf)
  · use (G.replaceVertex s t).replaceVertex s u, inferInstance
    exact ⟨(cf.replaceVertex s t).replaceVertex s u,
      card_lt_card_replaceVertex2 _ hst hsu hmax z.1 z.2⟩
  · rw [Decidable.not_and_iff_or_not_not] at z
    cases' z with st su
    · cases' lt_or_gt_of_ne st with less more
      · use G.replaceVertex t s, inferInstance
        rw [adj_comm] at hst
        exact ⟨cf.replaceVertex t s, G.card_lt_card_replaceVertex1 hst less⟩
      · use G.replaceVertex s t, inferInstance
        exact ⟨cf.replaceVertex s t, G.card_lt_card_replaceVertex1 hst more⟩
    · cases' lt_or_gt_of_ne su with less more
      · use G.replaceVertex u s, inferInstance
        rw [adj_comm] at hsu
        exact ⟨cf.replaceVertex u s, G.card_lt_card_replaceVertex1 hsu less⟩
      · use G.replaceVertex s u, inferInstance
        exact ⟨cf.replaceVertex s u, G.card_lt_card_replaceVertex1 hsu more⟩

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
theorem notAdj_equivalence : Equivalence fun x y => ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact G.not_adj_transitive hmax xy yz

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph that exists
because of `notAdj_equivalence`. Said graph is therefore a complete multipartite graph. -/
def notAdjSetoid : Setoid V := ⟨_, (notAdj_equivalence hmax)⟩

instance : DecidableRel (notAdjSetoid hmax).r :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

/-- The finpartition derived from `notAdjSetoid`. -/
def notAdjFinpartition : Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid (notAdjSetoid hmax)

theorem degree_eq_fintype_card_sub_part_card : G.degree s = Fintype.card V -
    ((notAdjFinpartition hmax).part (mem_univ s)).card := by
  calc
    G.degree s = (univ.filter (fun b => G.Adj s b)).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter (fun b => ¬G.Adj s b)).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert (Finpartition.mem_part_ofSetoid_iff_rel).symm
      simp [notAdjSetoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
theorem notAdj_equipartition : (notAdjFinpartition hmax).IsEquipartition := by
  let fp := notAdjFinpartition hmax
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  have large_eq : large = fp.part (a := w) (mem_univ _) :=
    (fp.existsUnique_mem (a := w) (mem_univ _)).unique
      ⟨hl, hw⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have small_eq : small = fp.part (a := v) (mem_univ _) :=
    (fp.existsUnique_mem (a := v) (mem_univ _)).unique
      ⟨hs, hv⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro cf
    use G.replaceVertex v w, inferInstance
    refine' ⟨cf.replaceVertex v w, _⟩
    have ha : G.Adj v w := by
      have lsn : large ≠ small := fun _ => by simp_all only [add_lt_iff_neg_left, not_lt_zero']
      contrapose! lsn
      have : _ ∈ fp.part _ ↔ ¬G.Adj v w := Finpartition.mem_part_ofSetoid_iff_rel
      exact fp.eq_of_mem_parts hl hs hw (small_eq ▸ this.mpr lsn)
    rw [G.card_edgeFinset_replaceVertex_of_adj ha]
    have large_le : large.card ≤ Fintype.card V := by
      simpa using card_le_card large.subset_univ
    have small_le : small.card ≤ Fintype.card V := by
      simpa using card_le_card small.subset_univ
    rw [degree_eq_fintype_card_sub_part_card, ← small_eq,
      degree_eq_fintype_card_sub_part_card, ← large_eq,
      Nat.add_sub_assoc (by rw [tsub_le_tsub_iff_left small_le]; linarith),
      tsub_tsub_tsub_cancel_left large_le, Nat.add_sub_assoc (lt_tsub_iff_left.mpr ineq).le]
    linarith [tsub_pos_iff_lt.mpr (lt_tsub_iff_left.mpr ineq)]
  contradiction

theorem notAdj_card_parts_le : (notAdjFinpartition hmax).parts.card ≤ r := by
  let fp := notAdjFinpartition hmax
  by_contra! h
  let z := fp.reprs -- `z` is an `r + 1`-clique in `G`
  have ncf : ¬G.CliqueFree z.card := by
    apply IsNClique.not_cliqueFree (s := z)
    constructor
    swap; · rfl
    intro v hv w hw hn
    norm_cast at hv hw
    contrapose! hn
    exact fp.reprs_injective hv hw (fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _)
      (Finpartition.mem_part_ofSetoid_iff_rel.mpr hn) (fp.mem_part _))
  rw [Finpartition.card_reprs] at ncf
  exact absurd (CliqueFree.mono (Nat.succ_le_of_lt h) hmax.1) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
The `min` is necessary because `r` may be greater than `n`, in which case `G` is complete but
still `r + 1`-cliquefree for having insufficiently many vertices. -/
theorem notAdj_card_parts : (notAdjFinpartition hmax).parts.card = min (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  apply le_antisymm (le_min fp.card_parts_le_card (notAdj_card_parts_le _))
  by_contra! h
  rw [lt_min_iff] at h
  obtain ⟨x, _, y, _, hn, he⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a => fp.part (a := a) (by simp)) univ fp.parts h.1 (fun _ _ => fp.part_mem _)
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro
    use G ⊔ edge x y, inferInstance
    have cf : G.CliqueFree r := by
      simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
        forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff]
      intro z zc
      obtain ⟨x', xm, y', ym, hn', he'⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
        (f := fun a => fp.part (a := a) (by simp)) z fp.parts (zc.symm ▸ h.2)
        (fun _ _ => fp.part_mem _)
      unfold Set.Pairwise; push_neg; norm_cast
      use x', xm, y', ym, hn'
      change (notAdjSetoid hmax).r x' y'
      apply Finpartition.mem_part_ofSetoid_iff_rel.mp
      exact he' ▸ fp.mem_part _
    refine' ⟨cf.sup_edge x y, _⟩
    convert Nat.lt.base G.edgeFinset.card
    convert G.card_edgeFinset_sup_edge _ hn
    change (notAdjSetoid hmax).r x y
    apply Finpartition.mem_part_ofSetoid_iff_rel.mp
    exact he ▸ fp.mem_part _
  contradiction

/-- **Turán's theorem**, forward direction.
Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
noncomputable def IsTuranMaximal.isoTuranGraph : G ≃g turanGraph (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  obtain ⟨zm, zp⟩ := (notAdj_equipartition hmax).partPreservingEquiv
  use (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  rw [← not_iff_not]
  change _ ↔ (notAdjSetoid hmax).r a b
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change _ ↔ b ∈ fp.part _
  have pe : b ∈ fp.part (mem_univ a) ↔ fp.part (mem_univ a) = fp.part (mem_univ b) := by
    constructor <;> intro h
    · exact fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _) h (fp.mem_part _)
    · rw [h]; exact fp.mem_part _
  rw [pe, zp ⟨a, mem_univ _⟩ ⟨b, mem_univ _⟩, notAdj_card_parts, not_not, min_comm]
  rcases le_or_lt r (Fintype.card V) with h | h
  · rw [min_eq_left h]; rfl
  · rw [min_eq_right h.le]
    have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ _⟩).2
    have cn0 : Fintype.card V ≠ 0 := by by_contra h; exact absurd (h ▸ lc a) not_lt_zero'
    have rn0 : r ≠ 0 := by linarith
    rw [(Nat.mod_eq_iff_lt cn0).mpr (lc a), (Nat.mod_eq_iff_lt cn0).mpr (lc b),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc a).trans h),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc b).trans h)]
    rfl

end Forward

section Reverse

variable (hr : 0 < r)

lemma restrictSubtype_cliqueFree (hmax : G.IsTuranMaximal r) (K : Finset V) :
    (G.restrictSubtype Kᶜ).CliqueFree (r + 1) := by
  by_contra ncf; unfold CliqueFree at ncf; push_neg at ncf; obtain ⟨Q, hQ⟩ := ncf
  have nq := hQ.map (f := ⟨Subtype.val, Subtype.val_injective⟩)
  rw [restrictSubtype_map] at nq
  exact absurd hmax.1 (nq.mono (G.restrictSubset_le Kᶜ)).not_cliqueFree

open Classical in
lemma restrictSubtype_compl_edgeFinset_card {m} (H : SimpleGraph (Fin (m + r)))
    (itm : H.IsTuranMaximal r) (K : Finset (Fin (m + r))) (Kc : K.card = r)
    (ih : (turanGraph m r).IsTuranMaximal r) :
    (H.restrictSubtype Kᶜ).edgeFinset.card ≤ (turanGraph m r).edgeFinset.card := by
  let S := H.restrictSubtype Kᶜ
  have Sc : Fintype.card { x // x ∈ Kᶜ } = m := by simp [Kc]
  let S' := S.overFin Sc
  let I := S.overFinIso Sc
  have card_eq : S'.edgeFinset.card = S.edgeFinset.card := by
    apply card_eq_of_equiv; simp only [Set.mem_toFinset]; exact I.mapEdgeSet.symm
  exact card_eq ▸ ih.2 S' ((H.restrictSubtype_cliqueFree itm K).comap I.symm)

open Classical BigOperators in
lemma sum_card_filter_adj_le_sub_mul {m} (H : SimpleGraph (Fin (m + r)))
    (cf : H.CliqueFree (r + 1)) (K : Finset (Fin (m + r))) (Kp : H.IsNClique r K) :
    ∑ b in Kᶜ, card (filter (fun x ↦ Adj H x b) K) ≤ (r - 1) * m := by
  suffices ∀ b ∈ Kᶜ, ∃ a ∈ K, ¬H.Adj a b by
    have lt : ∀ b ∈ Kᶜ, (K.filter (H.Adj · b)).card ≤ r - 1 := by
      intro b mb
      simp_rw [← Nat.lt_add_one_iff, Nat.sub_add_cancel hr, ← Kp.2]
      conv_rhs => rw [← filter_card_add_filter_neg_card_eq_card (H.Adj · b)]
      rw [Nat.lt_add_right_iff_pos, card_pos]
      obtain ⟨w, wp⟩ := this b mb
      use w; exact mem_filter.mpr wp
    convert sum_le_sum lt
    rw [sum_const, smul_eq_mul, card_compl, Kp.2, Fintype.card_fin, add_tsub_cancel_right,
      mul_comm]
  by_contra! l; obtain ⟨b, _, pp⟩ := l
  simp_rw [adj_comm] at pp
  exact absurd cf (Kp.insert pp).not_cliqueFree

open Classical in
lemma card_edgeFinset_le_card_turanGraph_calc {m} (H : SimpleGraph (Fin (m + r)))
    (itm : H.IsTuranMaximal r) (ncf : ¬H.CliqueFree r)
    (ih : (turanGraph m r).IsTuranMaximal r) :
    card (edgeFinset H) ≤ card (edgeFinset (turanGraph (m + r) r)) := by
  rw [CliqueFree] at ncf; push_neg at ncf; obtain ⟨K, Kp⟩ := ncf
  have Kc : K.card = r := Kp.2
  simp_rw [H.edgeFinset_decompose_card K, ← restrictSubtype_edgeFinset_card,
    betweenSubset_edgeFinset_card, card_edgeFinset_turanGraph_add hr]
  rw [add_right_comm (r.choose 2)]; gcongr
  · convert card_edgeFinset_le_card_choose_two
    · rw [Fintype.card_coe, Kc]
  · convert H.restrictSubtype_compl_edgeFinset_card (by convert itm) K Kc ih
  · exact H.sum_card_filter_adj_le_sub_mul hr itm.1 K Kp

/-- `turanGraph n r` is Turán-maximal *per se* (if `0 < r`). -/
theorem isTuranMaximal_turanGraph' : (turanGraph n r).IsTuranMaximal r := by
  suffices r = 0 ∨ (turanGraph n r).IsTuranMaximal r by
    exact this.resolve_left (by intro a; exact absurd a hr.ne')
  apply Nat.mod.inductionOn (motive := fun n r ↦ r = 0 ∨ (turanGraph n r).IsTuranMaximal r)
  · intro n r ⟨hr, b⟩ ih
    rw [Nat.eq_add_of_sub_eq b rfl]
    replace ih := ih.resolve_left hr.ne'
    apply Or.inr
    refine' ⟨turanGraph_cliqueFree hr, _⟩
    intro H _ cf
    wlog itm : H.IsTuranMaximal r generalizing H
    · obtain ⟨S, Z⟩ := exists_IsTuranMaximal (V := Fin _) hr
      classical exact (Z.2 H cf).trans (this S Z.1 Z)
    have ncf := H.not_cliqueFree_of_isTuranMaximal (r := r) hr (by simp)
    convert card_edgeFinset_le_card_turanGraph_calc hr H (by convert itm) (ncf itm) ih
  · intro n r b
    simp only [not_and, not_le] at b
    cases' r.eq_zero_or_pos with hr hr
    · exact Or.inl hr
    · exact Or.inr <| isTuranMaximal_turanGraph hr (b hr).le

/-- **Turán's theorem**, reverse direction.
Any graph isomorphic to `turanGraph n r` is itself Turán-maximal. -/
theorem isTuranMaximal_of_iso (iso : G ≃g turanGraph n r) : G.IsTuranMaximal r := by
  obtain ⟨p1, p2⟩ := isTuranMaximal_turanGraph' (n := n) hr
  have cV := iso.card_eq
  rw [Fintype.card_fin] at cV
  constructor
  · exact p1.comap iso
  · intro H _ cf
    let tr := H.overFinIso cV
    classical rw [iso.card_edgeFinset_eq, tr.card_edgeFinset_eq]
    convert p2 (H.overFin cV) (cf.comap tr.symm)

end Reverse

/-- **Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices. -/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r) := by
  constructor <;> intro h
  · exact ⟨h.isoTuranGraph⟩
  · obtain ⟨iso⟩ := h
    exact G.isTuranMaximal_of_iso hr iso

end SimpleGraph
