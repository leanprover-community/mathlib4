/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`.
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared. We give this proof below, see `colorable_of_cliqueFree_lt_minDegree`.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v, w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
 `t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

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

The vertex set of an `IsFiveWheel` structure `Wᵣ,ₖ` is `{v, w₁, w₂} ∪ s ∪ t : Finset α`.
We will need to refer to this consistently and choose the following formulation:
`{v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))` which is definitionally equal to
`insert v <| insert w₁ <| insert w₂ <| s ∪ t`.

## References

* [B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2][andrasfaiErdosSos1974]

* [S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z][brandt2003]
-/

local notation "‖" x "‖" => Fintype.card x

open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : ℕ}

namespace SimpleGraph

section withDecEq
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
`(r + 1)`-cliques and `#(s ∩ t) = k`. (If `G` is maximally `(r + 2)`-clique-free and not complete
multipartite then `G` will contain such a structure: see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`.)
-/
@[grind]
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
  exact ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8, rfl⟩

/-- `G.FiveWheelLikeFree r k` means there is no `IsFiveWheelLike r k` structure in `G`. -/
def FiveWheelLikeFree (G : SimpleGraph α) (r k : ℕ) : Prop :=
  ∀ {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

@[symm] lemma symm : G.IsFiveWheelLike r k v w₂ w₁ t s :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4, hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

@[grind →]
lemma fst_notMem_right : w₁ ∉ t :=
  fun h ↦ hw.isPathGraph3Compl.not_adj_fst <| hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

@[grind →]
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

@[grind →]
lemma card_left : s.card = r := by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

@[grind →]
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

end withDecEq

section AES
variable {i j n : ℕ} {d x v w₁ w₂ : α} {s t : Finset α}

section Counting

/--
Given lower bounds on non-adjacencies from `W` into `X`,`Xᶜ` we can bound the degree sum over `W`.
-/
private lemma sum_degree_le_of_le_not_adj [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
    {W X : Finset α} (hx : ∀ x ∈ X, i ≤ #{z ∈ W | ¬ G.Adj x z})
    (hxc : ∀ y ∈ Xᶜ, j ≤ #{z ∈ W | ¬ G.Adj y z}) :
    ∑ w ∈ W, G.degree w ≤ #X * (#W - i) + #Xᶜ * (#W - j) := calc
  _ = ∑ v, #(G.neighborFinset v ∩ W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (by simp [and_comm, adj_comm])
  _ ≤ _ := by
    simp_rw [← union_compl X, sum_union disjoint_compl_right (s₁ := X), neighborFinset_eq_filter,
             filter_inter, univ_inter, card_eq_sum_ones X, card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    gcongr <;> grind [filter_card_add_filter_neg_card_eq_card]

end Counting

namespace IsFiveWheelLike

variable [DecidableEq α] (hw : G.IsFiveWheelLike r k v w₁ w₂ s t) (hcf : G.CliqueFree (r + 2))

include hw hcf

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all of its common
 clique vertices then there exist (not necessarily distinct) vertices `a, b, c, d`, one from each of
 the four `r + 1`-cliques of `Wᵣ,ₖ`, none of which are adjacent to `x`.
-/
private lemma exist_not_adj_of_adj_inter (hW : ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y) :
    ∃ a b c d, a ∈ insert w₁ s ∧ ¬ G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬ G.Adj x b ∧ c ∈ insert v s ∧
    ¬ G.Adj x c ∧ d ∈ insert v t ∧ ¬ G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨a, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨b, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨c, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨d, hd, hdj⟩ := hw.isNClique_right.exists_not_adj_of_cliqueFree_succ hcf x
  exact ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, by grind⟩

variable [DecidableRel G.Adj]

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all but at most
two vertices of `Wᵣ,ₖ`, including all of its common clique vertices, then `G` contains a `Wᵣ,ₖ₊₁`.
-/
lemma exists_isFiveWheelLike_succ_of_not_adj_le_two (hW : ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y)
    (h2 : #{z ∈ {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))) | ¬ G.Adj x z} ≤ 2) :
    ∃ a b, G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter hcf hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))
  have ⟨hca, hdb⟩ : c = a ∧ d = b := by
    by_contra! hf
    apply h2.not_gt <| two_lt_card_iff.2 _
    by_cases h : a = c
    · exact ⟨a, b, d, by grind⟩
    · exact ⟨a, b, c, by grind⟩
  simp_rw [hca, hdb, mem_insert] at *
  have ⟨has, hbt, hav, hbv, haw, hbw⟩ : a ∈ s ∧ b ∈ t ∧ a ≠ v ∧ b ≠ v ∧ a ≠ w₂ ∧ b ≠ w₁ := by grind
  have ⟨hxv, hxw₁, hxw₂⟩ : v ≠ x ∧ w₁ ≠ x ∧ w₂ ≠ x := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · grind
      · exact haj <| hw.isNClique_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · grind
      · exact haj <| hw.isNClique_fst_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · grind
      · exact hbj <| hw.isNClique_snd_right.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  -- Since `x` is not adjacent to `a` and `b` but is adjacent to all but at most two vertices
  -- from `W` we have `∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x`
  have wa : ∀ ⦃w⦄, w ∈ W → w ≠ a → w ≠ b → G.Adj w x := by
    intro _ hz haz hbz
    by_contra! hf
    apply h2.not_gt
    exact two_lt_card.2 ⟨_, by simp [has, hcj], _, by simp [hbt, hdj], _,
                         mem_filter.2 ⟨hz, by rwa [adj_comm] at hf⟩, hab, haz.symm, hbz.symm⟩
  have ⟨h1s, h2t⟩ : insert w₁ s ⊆ W ∧ insert w₂ t ⊆ W := by grind
  -- We now check that we can build a `Wᵣ,ₖ₊₁` by inserting `x` and erasing `a` and `b`
  refine ⟨a, b, ⟨by grind, by grind, by grind, by grind, by grind, ?h5, ?h6, ?h7, ?h8, ?h9⟩⟩
  -- Check that the new cliques are indeed cliques
  case h5 => exact hw.isNClique_left.insert_insert_erase has hw.notMem_left fun _ hz hZ ↦
               wa ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz) hZ
                 fun h ↦ hbv <| (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h6 => exact hw.isNClique_fst_left.insert_insert_erase has hw.fst_notMem fun _ hz hZ ↦
               wa (h1s hz) hZ fun h ↦ hbw <| (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h7 => exact hw.isNClique_right.insert_insert_erase hbt hw.notMem_right fun _ hz hZ ↦
               wa ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz)
                 (fun h ↦ hav <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h8 => exact hw.isNClique_snd_right.insert_insert_erase hbt hw.snd_notMem fun _ hz hZ ↦
               wa (h2t hz) (fun h ↦  haw <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h9 =>
    -- Finally check that this new `IsFiveWheelLike` structure has `k + 1` common clique
    -- vertices i.e. `#((insert x (s.erase a)) ∩ (insert x (s.erase b))) = k + 1`.
    rw [← insert_inter_distrib, erase_inter, inter_erase, erase_eq_of_notMem <|
        notMem_mono inter_subset_left hbs, erase_eq_of_notMem <| notMem_mono inter_subset_right hat,
        card_insert_of_notMem (fun h ↦ G.irrefl (hW h)), hw.card_inter]

/--
If `G` is a `Kᵣ₊₂`-free graph with `n` vertices containing a `Wᵣ,ₖ` but no `Wᵣ,ₖ₊₁`
then `G.minDegree ≤ (2 * r + k) * n / (2 * r + k + 3)`
-/
lemma minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ [Fintype α]
    (hm : G.FiveWheelLikeFree r (k + 1)) : G.minDegree ≤ (2 * r + k) * ‖α‖ / (2 * r + k + 3) := by
  let X : Finset α := {x | ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y}
  let W := {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : ∀ x ∈ X, 3 ≤ #{z ∈ W | ¬ G.Adj x z} := by
    intro _ hx
    by_contra! h
    obtain ⟨_, _, hW⟩ := hw.exists_isFiveWheelLike_succ_of_not_adj_le_two hcf
      (by simpa [X] using hx) <| Nat.le_of_succ_le_succ h
    exact hm hW
  -- Since `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ`, every vertex is not adjacent to at least one
  -- wheel vertex.
  have one_le (x : α) : 1 ≤ #{z ∈ {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))) | ¬ G.Adj x z} :=
    let ⟨_, hz⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
    card_pos.2 ⟨_, mem_filter.2 ⟨by grind, hz.2⟩⟩
  -- Since every vertex has at least one non-neighbor in `W` we now have the following upper bound
  -- `∑ w ∈ W, H.degree w ≤ #X * (#W - 3) + #Xᶜ * (#W - 1)`
  have bdW := sum_degree_le_of_le_not_adj dXle (fun y _ ↦ one_le y)
  -- By the definition of `X`, any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : ∀ x ∈ Xᶜ, 1 ≤ #{z ∈ s ∩ t | ¬ G.Adj x z} := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : ∃ y ∈ s ∩ t, ¬ G.Adj x y := by
      contrapose! hx
      simpa [X] using hx
    exact ⟨_, mem_filter.2 hy⟩
  -- So we also have an upper bound on the degree sum over `s ∩ t`
  -- `∑ w ∈ s ∩ t, H.degree w ≤ #Xᶜ * (#(s ∩ t) - 1) + #X * #(s ∩ t)`
  have bdX := sum_degree_le_of_le_not_adj xcle (fun _ _ ↦ Nat.zero_le _)
  rw [compl_compl, tsub_zero, add_comm] at bdX
  rw [Nat.le_div_iff_mul_le <| Nat.add_pos_right _ zero_lt_three]
  have Wc : #W + k = 2 * r + 3 := by
    change #(insert _ <| insert _ <| insert _ _) + _ = _
    grind [card_inter_add_card_union]
  -- The sum of the degree sum over `W` and twice the degree sum over `s ∩ t`
  -- is at least `G.minDegree * (#W + 2 * #(s ∩ t))` which implies the result
  calc
    _ ≤ ∑ w ∈ W, G.degree w + 2 * ∑ w ∈ s ∩ t, G.degree w := by
      simp_rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add,
               ← hw.card_inter, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one, mul_comm 2]
      gcongr with i <;> exact minDegree_le_degree ..
    _ ≤ #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by grind
    _ ≤ _ := by
        by_cases hk : k = 0 -- so `s ∩ t = ∅` and hence `Xᶜ = ∅`
        · have Xu : X = univ := by
            rw [← hw.card_inter, card_eq_zero] at hk
            exact eq_univ_of_forall fun _ ↦ by simp [X, hk]
          subst k
          rw [add_zero] at Wc
          simp [Xu, Wc, mul_comm]
        have w3 : 3 ≤ #W := two_lt_card.2 ⟨_, mem_insert_self .., _, by simp [W], _, by simp [W],
          hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩
        have hap : #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by omega
        rw [hap, ← add_mul, card_add_card_compl, mul_comm, two_mul, ← add_assoc]
        gcongr
        cutsat

end IsFiveWheelLike

variable [DecidableEq α]

/-- **Andrasfái-Erdős-Sós** theorem

If `G` is a `Kᵣ₊₁`-free graph with `n` vertices and `(3 * r - 4) * n / (3 * r - 1) < G.minDegree`
then `G` is `r + 1`-colorable, e.g. if `G` is `K₃`-free and `2 * n / 5 < G.minDegree` then `G`
is `2`-colorable.
-/
theorem colorable_of_cliqueFree_lt_minDegree [Fintype α] [DecidableRel G.Adj]
    (hf : G.CliqueFree (r + 1)) (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) :
    G.Colorable r := by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    -- There is an edge maximal `Kᵣ₊₃`-free supergraph `H` of `G`
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H ↦ H.CliqueFree (r + 3)) G hf
    -- If `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mono_left hle
    -- Suppose, for a contradiction, that `H` is not `r + 2`-colorable
    by_contra! hnotcol
    -- so `H` is not complete-multipartite
    have hn : ¬ H.IsCompleteMultipartite := fun hc ↦ hnotcol <| hc.colorable_of_cliqueFree hmcf.1
    -- Hence `H` contains `Wᵣ₊₁,ₖ` but not `Wᵣ₊₁,ₖ₊₁`, for some `k < r + 1`
    obtain ⟨k, _, _, _, _, _, hw, hlt, hm⟩ :=
      exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite hmcf hn
    classical
    -- But the minimum degree of `G`, and hence of `H`, is too large for it to be `Wᵣ₊₁,ₖ₊₁`-free,
    -- a contradiction.
    have hD := hw.minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ hmcf.1 <| hm _ <| lt_add_one _
    have : (2 * (r + 1) + k) * ‖α‖ / (2 * (r + 1) + k + 3) ≤ (3 * r + 2) * ‖α‖ / (3 * r + 5) := by
      apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
              <| (mul_le_mul_iff_right₀ (_ + 2).succ_pos).1 _
      rw [← mul_assoc, mul_comm (2 * r + 2 + k + 3), mul_comm _ (_ * ‖α‖)]
      apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
      nlinarith
    exact (hd.trans_le <| minDegree_le_minDegree hle).not_ge <| hD.trans <| this

end AES
end SimpleGraph
