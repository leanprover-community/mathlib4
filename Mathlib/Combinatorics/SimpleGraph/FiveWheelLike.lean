/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v , w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
 `t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k  = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

The first interesting cases of such structures are `W₁,₀` and `W₂,₁`: `W₁,₀` is a 5-cycle,
while `W₂,₁` is a 5-cycle with an extra central hub vertex adjacent to all other vertices
(i.e. `W₂,₁` resembles a wheel with five spokes).

                 `W₁,₀`       v                 `W₂,₁`      v
                           /     \                       /  |  \
                          s       t                     s ─ u ─ t
                           \     /                       \ / \ /
                           w₁ ─ w₂                       w₁ ─ w₂

## Main definitions

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of
  `G` with `r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
  `#(s ∩ t) = k`.

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## Implementation notes
The definitions of `IsFiveWheelLike` and `IsFiveWheelLikeFree` in this file have `r` shifted by two
compared to the definitions in Brandt **On the structure of graphs with bounded clique number**

The definition of `IsFiveWheelLike` does not contain the facts that `#s = r` and `#t = r` but we
deduce these later as `card_left` and `card_right`.

Although `#(s ∩ t)` can easily be derived from `s` and `t` we include the `IsFiveWheelLike` field
`card_inter : #(s ∩ t) = k` to match the informal / paper definitions and to simplify some
statements of results and match our definition of `IsFiveWheelLikeFree`.

## References

* [B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2][andrasfaiErdosSos1974]

* [S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z][brandt2003]
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
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

/--
An `IsFiveWheelLike r k v w₁ w₂ s t` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets
`s` and `t` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they form an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s ∪ t`, `s ∪ {v}, t ∪ {v}, s ∪ {w₁}, t ∪ {w₂}` are all
`(r + 1)`- cliques and `#(s ∩ t) = k`. (If `G` is maximally `(r + 2)`-cliquefree and not complete
multipartite then `G` will contain such a structure : see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`.)
-/
structure IsFiveWheelLike (G : SimpleGraph α) (r k : ℕ) (v w₁ w₂ : α) (s t : Finset α) :
    Prop where
  /-- `{v, w₁, w₂}` induces the single edge `w₁w₂` -/
  isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
  notMem_left : v ∉ s
  notMem_right : v ∉ t
  fst_notMem : w₁ ∉ s
  snd_notMem : w₂ ∉ t
  isNClique_left : G.IsNClique (r + 1) (insert v s)
  isNClique_fst_left : G.IsNClique (r + 1) (insert w₁ s)
  isNClique_right : G.IsNClique (r + 1) (insert v t)
  isNClique_snd_right : G.IsNClique (r + 1) (insert w₂ t)
  card_inter : #(s ∩ t) = k

lemma exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ v w₁ w₂ s t, G.IsFiveWheelLike r #(s ∩ t) v w₁ w₂ s t := by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨t, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact  ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8, rfl⟩

/-- `G.FiveWheelLikeFree r k` means there is no `IsFiveWheelLike r k` structure in `G`. -/
def FiveWheelLikeFree (G : SimpleGraph α) (r k : ℕ) : Prop :=
  ∀ {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

@[symm] lemma symm : G.IsFiveWheelLike r k v w₂ w₁ t s :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4 , hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

lemma fst_notMem_right : w₁ ∉ t :=
  fun h ↦ hw.isPathGraph3Compl.not_adj_fst <| hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

lemma snd_notMem_left : w₂ ∉ s := hw.symm.fst_notMem_right

/--
Any graph containing an `IsFiveWheelLike r k` structure is not `(r + 1)`-colorable.
-/
lemma not_colorable_succ : ¬ G.Colorable (r + 1) := by
  intro ⟨C⟩
  have h := C.surjOn_of_card_le_isClique hw.isNClique_fst_left.1 (by simp [hw.isNClique_fst_left.2])
  have := C.surjOn_of_card_le_isClique hw.isNClique_snd_right.1 (by simp [hw.isNClique_snd_right.2])
  -- Since `C` is an `r + 1`-coloring and `insert w₁ s` is an `r + 1`-clique, it contains a vertex
  -- `x` which shares its colour with `v`
  obtain ⟨x, hx, hcx⟩ := h (a := C v) trivial
  -- Similarly there is a vertex `y` in `insert w₂ t` which shares its colour with `v`.
  obtain ⟨y, hy, hcy⟩ := this (a := C v) trivial
  rw [coe_insert] at *
  -- However since `insert v s` and `insert v t` are cliques, we must have `x = w₁` and `y = w₂`.
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy =>
    -- But this is a contradiction since `w₁` and `w₂` are adjacent.
      subst_vars; exact C.valid hw.isPathGraph3Compl.adj (hcy ▸ hcx)
    | inr hy =>
      apply (C.valid _ hcy.symm).elim
      exact hw.isNClique_right.1 (by simp) (by simp [hy]) fun h ↦ hw.notMem_right (h ▸ hy)
  | inr hx =>
    apply (C.valid _ hcx.symm).elim
    exact hw.isNClique_left.1 (by simp) (by simp [hx]) fun h ↦ hw.notMem_left (h ▸ hx)

lemma card_left : s.card = r := by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

lemma card_right : t.card = r := hw.symm.card_left

lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : k < r := by
  contrapose! h
  -- If `r ≤ k` then `s = t` and so `s ∪ {w₁, w₂}` is an `r + 2`-clique, a contradiction.
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_inter ▸ hw.card_left ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_inter ▸ hw.card_right ▸ h)
  exact (hw.isNClique_fst_left.insert_insert (hs ▸ this.symm ▸ hw.isNClique_snd_right)
    hw.snd_notMem_left hw.isPathGraph3Compl.adj).not_cliqueFree

end IsFiveWheelLike

/--
Any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite contains a maximal
`IsFiveWheelLike` structure `Wᵣ,ₖ` for some `k < r`. (It is maximal in terms of `k`.)
-/
lemma exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ k v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t ∧ k < r ∧
      ∀ j, k < j → G.FiveWheelLikeFree r j := by
  obtain ⟨_, _, _, s, t, hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hnc
  let P : ℕ → Prop := fun k ↦ ∃ v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t
  have hk : P #(s ∩ t) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le hk
  exact ⟨_, _, _, _, _, _, hw, hw.card_inter_lt_of_cliqueFree h.1,
         fun _ hj _ _ _ _ _ hv ↦ hj.not_ge <| Nat.le_findGreatest
           (hv.card_inter_lt_of_cliqueFree h.1).le ⟨_, _, _, _, _, hv⟩⟩

lemma CliqueFree.fiveWheelLikeFree_of_le (h : G.CliqueFree (r + 2)) (hk : r ≤ k) :
    G.FiveWheelLikeFree r k := fun hw ↦ (hw.card_inter_lt_of_cliqueFree h).not_ge hk

/-- A maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is complete-multipartite. -/
theorem colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree
    (h : Maximal (fun H => H.CliqueFree (r + 1)) G) : G.Colorable r ↔ G.IsCompleteMultipartite := by
  match r with
  | 0 => exact ⟨fun _ ↦ fun x ↦ cliqueFree_one.1 h.1 |>.elim' x,
                fun _ ↦ G.colorable_zero_iff.2 <| cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc ↦ ?_, fun hc ↦ hc.colorable_of_cliqueFree h.1⟩
    contrapose! hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hc
    exact hw.not_colorable_succ

end SimpleGraph
