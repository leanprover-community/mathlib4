/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
/-!
If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Putting these together gives the definition of an `IsFiveWheelLike` structure
which can be found in any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite`).

We can use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
complete-multipartite : `colorable_iff_isCompleteMultipartite_of_max_cliqueFree`

They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
first appeared.

Main definitions :

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s₁ s₂` to form a 5-wheel-like subgraph of
 `G` with `r`-sets `s₁` and `s₂`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
 `#(s₁ ∩ s₂) = k`. (We denote this by `Wᵣ,ₖ` below in comments.)

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## References

  B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2

  S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z

-/
open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : ℕ}

namespace SimpleGraph

variable [DecidableEq α]

private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (ha : G.Adj a b) :
    G.IsNClique (r + 1) (insert b (insert a s)) := by
  apply h1.insert (fun b hb ↦ ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
  · exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) <| fun h' ↦ (h3 (h' ▸ h)).elim

private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c ∈ s)
    (ha : a ∉ s) (hd : ∀ w ∈ insert a s, w ≠ c → G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  rw [insert_comm, ← erase_insert_of_ne (fun h : a = c ↦ ha (h ▸ hc)|>.elim)]
  simp_rw [adj_comm, ← not_mem_singleton] at hd
  exact hs.insert_erase (fun _ h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

/--
An `IsFiveWheelLike r k v w₁ w₂ s₁ s₂` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets
`s₁` and `s₂` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they form an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s₁ ∪ s₂`, `s₁ ∪ {v}, s₂ ∪ {v}, s₁ ∪ {w₁}, s₂ ∪ {w₂}` are all
`(r + 1)`- cliques and `#(s₁ ∩ s₂) = k`. (If `G` is maximally `(r + 2)`-cliquefree and not complete
 multipartite then `G` will contain such a structure : see
`exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite`.)
-/
structure IsFiveWheelLike (G : SimpleGraph α) (r k : ℕ) (v w₁ w₂ : α) (s₁ s₂ : Finset α) :
    Prop where
  /-- `{v, w₁, w₂}` induces the single edge `w₁w₂` -/
  isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
  not_mem_fst : v ∉ s₁
  not_mem_snd : v ∉ s₂
  fst_not_mem : w₁ ∉ s₁
  snd_not_mem : w₂ ∉ s₂
  isNClique_fst : G.IsNClique (r + 1) (insert v s₁)
  isNClique_fst_fst : G.IsNClique (r + 1) (insert w₁ s₁)
  isNClique_snd : G.IsNClique (r + 1) (insert v s₂)
  isNClique_snd_snd : G.IsNClique (r + 1) (insert w₂ s₂)
  card_eq : #(s₁ ∩ s₂) = k

lemma exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r #(s₁ ∩ s₂) v w₁ w₂ s₁ s₂ := by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s₁, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨s₂, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact  ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8, rfl⟩

/-- `G.FiveWheelLikeFree r k` means there is no `IsFiveWheelLike r k` structure in `G`. -/
def FiveWheelLikeFree (G : SimpleGraph α) (r k : ℕ) : Prop :=
    ∀ {v w₁ w₂ s₁ s₂}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s₁ s₂

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {s₁ s₂ : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s₁ s₂)

include hw

@[symm] lemma symm : G.IsFiveWheelLike r k v w₂ w₁ s₂ s₁ :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4 , hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

lemma fst_not_mem_snd : w₁ ∉ s₂ :=
  fun h ↦ hw.isPathGraph3Compl.not_adj_fst <| hw.isNClique_snd.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

/--
Any graph containing an `IsFiveWheelLike r k` structure is not `(r + 1)`-colorable.
-/
lemma not_colorable_succ : ¬ G.Colorable (r + 1) := by
  intro ⟨C⟩
  have h1 := C.surjOn_of_card_le_isClique hw.isNClique_fst_fst.1 (by simp [hw.isNClique_fst_fst.2])
  have h2 := C.surjOn_of_card_le_isClique hw.isNClique_snd_snd.1 (by simp [hw.isNClique_snd_snd.2])
  obtain ⟨x, hx, hcx⟩ := h1 (a := C v) trivial
  obtain ⟨y, hy, hcy⟩ := h2 (a := C v) trivial
  rw [coe_insert] at *
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy => subst_vars; exact C.valid hw.isPathGraph3Compl.adj (hcy ▸ hcx)
    | inr hy =>
      apply (C.valid _ hcy.symm).elim
      exact hw.isNClique_snd.1 (by simp) (by simp [hy]) fun h ↦ hw.not_mem_snd (h ▸ hy)
  | inr hx =>
      apply (C.valid _ hcx.symm).elim
      exact hw.isNClique_fst.1 (by simp) (by simp [hx]) fun h ↦ hw.not_mem_fst (h ▸ hx)

lemma card_isNClique_erase : s₁.card = r := by
  simp [← Nat.succ_inj, ← hw.isNClique_fst.2, hw.not_mem_fst]

lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : k < r := by
  contrapose! h
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_eq ▸ hw.card_isNClique_erase ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_eq ▸ hw.symm.card_isNClique_erase ▸ h)
  exact (hw.isNClique_fst_fst.insert_insert (hs ▸ this.symm ▸ hw.isNClique_snd_snd)
    hw.symm.fst_not_mem_snd hw.isPathGraph3Compl.adj).not_cliqueFree

end IsFiveWheelLike

/--
Any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite contains a maximal
`IsFiveWheelLike` stucture `Wᵣ,ₖ` for some `k < r`. (It is maximal in terms of `k`.)
-/
lemma exists_max_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ k v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r k v w₁ w₂ s₁ s₂ ∧ k < r ∧
    ∀ j, k < j → G.FiveWheelLikeFree r j := by
  obtain ⟨_, _, _, s₁, s₂, hw⟩ :=
    exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite h hnc
  let P : ℕ → Prop := fun k ↦ ∃ v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r k v w₁ w₂ s₁ s₂
  have hk : P #(s₁ ∩ s₂) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le hk
  exact ⟨_, _, _, _, _, _, hw, hw.card_inter_lt_of_cliqueFree h.1,
         fun _ hj _ _ _ _ _ hv ↦ Nat.lt_le_asymm hj
           <| Nat.le_findGreatest (hv.card_inter_lt_of_cliqueFree h.1).le ⟨_, _, _, _, _, hv⟩⟩

lemma CliqueFree.fiveWheelLikeFree_of_le (h : G.CliqueFree (r + 2)) (hk : r ≤ k) :
    G.FiveWheelLikeFree r k := fun hw ↦ Nat.lt_le_asymm (hw.card_inter_lt_of_cliqueFree h) hk

/-- A maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is complete-multipartite. -/
theorem colorable_iff_isCompleteMultipartite_of_max_cliqueFree
    (h : Maximal (fun H => H.CliqueFree (r + 1)) G) : G.Colorable r ↔ G.IsCompleteMultipartite := by
  match r with
  | 0 =>  exact ⟨fun _ ↦ fun x ↦ cliqueFree_one.1 h.1|>.elim' x,
                 fun _ ↦ G.colorable_zero_iff.2 <| cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc ↦ ?_, fun hc ↦ hc.colorable_of_cliqueFree h.1⟩
    contrapose! hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite h hc
    exact hw.not_colorable_succ

end SimpleGraph
