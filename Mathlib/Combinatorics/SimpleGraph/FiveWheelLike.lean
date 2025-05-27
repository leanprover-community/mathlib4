/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`.
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared: `colorable_of_cliqueFree_lt_minDegree`.

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

* B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2

* S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z
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

/-- Any `Wᵣ,ₖ` contains `2 * r + 3 - k` vertices, which we express here without subtraction. -/
lemma card_add_card_inter : #(insert v (insert w₁ (insert w₂ (s ∪ t)))) + k = 2 * r + 3 := by
  rw [add_comm, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem]
  · simp [← add_assoc, ← hw.card_inter, card_inter_add_card_union, two_mul, hw.card_left,
          hw.card_right]
  · simpa using ⟨hw.snd_notMem_left, hw.snd_notMem⟩
  · simpa using ⟨hw.isPathGraph3Compl.fst_ne_snd, hw.fst_notMem, hw.fst_notMem_right⟩
  · simpa using ⟨hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd,
                 hw.notMem_left, hw.notMem_right⟩

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
         fun _ hj _ _ _ _ _ hv ↦ hj.not_le <| Nat.le_findGreatest
           (hv.card_inter_lt_of_cliqueFree h.1).le ⟨_, _, _, _, _, hv⟩⟩

lemma CliqueFree.fiveWheelLikeFree_of_le (h : G.CliqueFree (r + 2)) (hk : r ≤ k) :
    G.FiveWheelLikeFree r k := fun hw ↦ (hw.card_inter_lt_of_cliqueFree h).not_le hk

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
variable {i j n : ℕ} {d x : α}

section Counting

private lemma kr_bound (hk : k ≤ r) :
    (2 * (r + 1) + k) * n / (2 * (r + 1) + k + 3) ≤ (3 * r + 2) * n / (3 * r + 5) := by
  apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
          <| (mul_le_mul_left (2 * r + 2 + k + 2).succ_pos).1 _
  rw [← mul_assoc, mul_comm (2 * r + 2 + k + 3), mul_comm _ (_ * n)]
  apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
  nlinarith

variable [DecidableRel G.Adj]

/-- Transform a lower bound on non-adjacencies into an upper bound on adjacencies. -/
private lemma card_adj_le_of_le_card_not_adj (hx : i ≤ #(s.filter (¬ G.Adj x ·))) :
    #(s.filter (G.Adj x ·)) ≤ #s - i := by
  rw [← filter_card_add_filter_neg_card_eq_card (s := s) (G.Adj x ·), add_tsub_assoc_of_le hx]
  exact Nat.le_add_right ..

variable [DecidableEq α]

/-- Useful trivial fact `|{a, b, c, d}| ≤ 2` given `a ≠ b`, `a ≠ d`, `b ≠ c`. -/
private lemma eq_of_card_le_two_of_ne (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c)
    (hc2 : #{a, b, c, d} ≤ 2) : c = a ∧ d = b := by
  by_contra! hf
  apply hc2.not_lt <| two_lt_card_iff.2 _
  by_cases h : a = c <;> aesop

/--
Given lower bounds on non-adjacencies from `W` into `X`,`Xᶜ` we can bound the degree sum over `W`.
-/
private lemma sum_degree_le_of_le_not_adj [Fintype α] {W X : Finset α}
    (hx : ∀ x, x ∈ X → i  ≤ #(W.filter (¬ G.Adj x ·)))
    (hxc : ∀ y, y ∈ Xᶜ → j ≤ #(W.filter (¬ G.Adj y ·))) :
    ∑ w ∈ W, G.degree w ≤ #X * (#W - i) + #Xᶜ * (#W - j) := calc
  _ = ∑ v, #(G.neighborFinset v ∩ W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (fun _ _ ↦ by simp [and_comm, adj_comm])
  _ ≤ _ := by
    rw [← union_compl X, sum_union disjoint_compl_right]
    simp_rw [neighborFinset_eq_filter, filter_inter, univ_inter, card_eq_sum_ones X,
      card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    apply add_le_add <;> apply sum_le_sum <;> intro x hx1
    · exact card_adj_le_of_le_card_not_adj <| hx x hx1
    · exact card_adj_le_of_le_card_not_adj <| hxc x hx1

end Counting

namespace IsFiveWheelLike

variable [DecidableEq α] {v w₁ w₂ : α} {s t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all of its common
 clique vertices then there exist (not necessarily distinct) vertices `a, b, c, d` that are not
adjacent to `x` and satisfy various conditions.
-/
private lemma exist_not_adj_of_adj_inter (h : G.CliqueFree (r + 2))
    (hW : ∀ {y}, y ∈ s ∩ t → G.Adj x y) :
    ∃ a b c d, a ∈ insert w₁ s ∧ ¬ G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬ G.Adj x b ∧ c ∈ insert v s ∧
    ¬ G.Adj x c ∧ d ∈ insert v t ∧ ¬ G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨_, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hd, hdj⟩ := hw.isNClique_right.exists_not_adj_of_cliqueFree_succ h x
  refine ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, ?_, ?_, ?_, ?_, ?_⟩
    <;> rw [mem_insert] at * <;> try rintro rfl
  · obtain (rfl | ha) := ha
    · obtain (rfl | hb) := hb
      · exact hw.isPathGraph3Compl.fst_ne_snd rfl
      · exact hw.fst_notMem_right hb
    · obtain (rfl | hb) := hb
      · exact hw.snd_notMem_left ha
      · exact haj <| hW <| mem_inter_of_mem ha hb
  · obtain (rfl | ha) := ha
    · obtain (rfl | hd) := hd
      · exact hw.isPathGraph3Compl.ne_fst rfl
      · exact hw.fst_notMem_right  hd
    · obtain (rfl | hd) := hd
      · exact hw.notMem_left ha
      · exact haj <| hW <| mem_inter_of_mem ha hd
  · obtain (rfl | hb) := hb
    · obtain (rfl | hc) := hc
      · exact hw.isPathGraph3Compl.ne_snd rfl
      · exact hw.snd_notMem_left hc
    · obtain (rfl | hc) := hc
      ·  exact hw.notMem_right hb
      ·  exact hbj <| hW <| mem_inter_of_mem hc hb
  · intro hat
    obtain (rfl | ha) := ha
    · exact hw.fst_notMem_right hat
    · exact haj <| hW <| mem_inter_of_mem ha hat
  · intro hbs
    obtain (rfl | hb) := hb
    · exact hw.snd_notMem_left hbs
    · exact hbj <| hW <| mem_inter_of_mem hbs hb

variable [DecidableRel G.Adj]

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all but at most
two vertices of `Wᵣ,ₖ`, including all of its common clique vertices, then `G` contains a `Wᵣ,ₖ₊₁`
(given by inserting `x` and erasing `a ∈ s \ t` and `b ∈ t \ s`).
-/
lemma exists_isFiveWheelLike_succ_of_not_adj_le_two (h : G.CliqueFree (r + 2))
    (hW : ∀ {y}, y ∈ s ∩ t → G.Adj x y)
    (h2 : #(({v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))).filter (¬ G.Adj x ·)) ≤ 2) :
    ∃ a b, G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter h hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := insert v <| insert w₁ <| insert w₂ (s ∪ t)
  have hfst := hw.isPathGraph3Compl.ne_fst
  have hsnd := hw.isPathGraph3Compl.ne_snd
  have ⟨hca, hdb⟩ : c = a ∧ d = b :=
    eq_of_card_le_two_of_ne hab had hbc <| h2.trans' <| card_le_card (fun _ ↦ (by aesop))
  simp_rw [hca, hdb, mem_insert] at *
  have has : a ∈ s := by
    obtain (rfl | ha) := ha
    · obtain (rfl | hc) := hc <;> trivial
    · exact ha
  have hbt: b ∈ t := by
    obtain (rfl | hb) := hb;
    · obtain (rfl | hd) := hd <;> trivial
    · exact hb
  have habv : v ≠ a ∧ v ≠ b := ⟨fun h ↦ hw.notMem_left (h ▸ has), fun h ↦ hw.notMem_right (h ▸ hbt)⟩
  have haw2 : a ≠ w₂ := fun hf ↦ hw.snd_notMem_left (hf ▸ has)
  have hbw1 : b ≠ w₁ := fun hf ↦ hw.fst_notMem_right (hf ▸ hbt)
  have ⟨hxv, hxw₁, hxw₂⟩ : v ≠ x ∧ w₁ ≠ x ∧ w₂ ≠ x := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.notMem_left (hax ▸ has)
      · exact haj <| hw.isNClique_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.fst_notMem (hax ▸ has)
      · exact haj <| hw.isNClique_fst_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · exact hw.snd_notMem (hbx ▸ hbt)
      · exact hbj <| hw.isNClique_snd_right.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  -- Since `x` is not adjacent to `a` and `b` but is adjacent to all but at most two vertices
  -- from `W` we have `∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x`
  have wadj : ∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x := by
    intro z hz haz hbz
    by_contra! hf
    apply h2.not_lt
    refine two_lt_card.2 ⟨a, ?_, b, ?_, z, ?_, hab, haz.symm, hbz.symm⟩ <;> rw [mem_filter]
    · exact ⟨mem_insert_of_mem <| mem_insert_of_mem <| mem_insert_of_mem <| mem_union_left _ has,
             hcj⟩
    · exact ⟨mem_insert_of_mem <| mem_insert_of_mem <| mem_insert_of_mem <| mem_union_right _ hbt,
             hdj⟩
    · exact ⟨hz, by rwa [adj_comm] at hf⟩
  have hc2 : insert w₁ s ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm]
    exact insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  have hc4 : insert w₂ t ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm w₁, insert_comm v]
    exact insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  -- We now check that we can build a `Wᵣ,ₖ₊₁` be inserting `x` and erasing `a` and `b`
  refine ⟨a, b, ⟨hw.isPathGraph3Compl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    <;> try rw [mem_insert, not_or]
  -- First check that `v, w₁, w₂` are not members of the new cliques
  · exact ⟨hxv, fun hv ↦ hw.notMem_left (mem_erase.1 hv).2⟩
  · exact ⟨hxv, fun hv ↦ hw.notMem_right (mem_erase.1 hv).2⟩
  · exact ⟨hxw₁, fun hw1 ↦ hw.fst_notMem (mem_erase.1 hw1).2⟩
  · exact ⟨hxw₂, fun hv ↦ hw.snd_notMem (mem_erase.1 hv).2⟩
  -- Next check that the new cliques are indeed cliques
  · apply hw.isNClique_left.insert_insert_erase has hw.notMem_left fun z hz hZ ↦
            wadj _ ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact habv.2.symm <| hz.resolve_right hbs
  · apply hw.isNClique_fst_left.insert_insert_erase has hw.fst_notMem fun z hz hZ ↦
            wadj _ (hc2 hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact hbw1 <| hz.resolve_right hbs
  · apply hw.isNClique_right.insert_insert_erase hbt hw.notMem_right fun z hz hZ ↦
            wadj _ ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact habv.1.symm <| hz.resolve_right hat
  · apply hw.isNClique_snd_right.insert_insert_erase hbt hw.snd_notMem
                      fun z hz hZ ↦ wadj _ (hc4 hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact haw2 <| hz.resolve_right hat
  · -- Finally we check that this new `IsFiveWheelLike` structure has `k + 1` common clique
    -- vertices and so is a copy of `Wᵣ,ₖ₊₁`
    rw [← insert_inter_distrib, erase_inter, inter_erase, erase_eq_of_notMem <|
        notMem_mono inter_subset_left hbs, erase_eq_of_notMem <| notMem_mono inter_subset_right hat,
        card_insert_of_notMem (fun h ↦ G.loopless _ (hW h)), hw.card_inter]

/--
If `G` is `Kᵣ₊₂`- free and contains a `Wᵣ,ₖ` then every vertex is not adjacent to at least one wheel
vertex.
-/
lemma one_le_not_adj_of_cliqueFree (hc : G.CliqueFree (r + 2)) (x : α) :
    1 ≤ #((({v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))))).filter (¬ G.Adj x ·)) := by
  apply card_pos.2
  obtain ⟨_, hz⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hc x
  exact ⟨_, mem_filter.2 ⟨by aesop, hz.2⟩⟩

/--
If `G` is a `Kᵣ₊₂`-free graph with `n` vertices containing a `Wᵣ,ₖ` but no `Wᵣ,ₖ₊₁`
then `G.minDegree ≤ (2 * r + k) * n / (2 * r + k + 3)`
-/
lemma minDegree_le_of_cliqueFree_FiveWheelLikeFree_succ [Fintype α] (hc : G.CliqueFree (r + 2))
    (hm : G.FiveWheelLikeFree r (k + 1)) : G.minDegree ≤ (2 * r + k) * ‖α‖ / (2 * r + k + 3) := by
  let X := {x | ∀ {y}, y ∈ s ∩ t → G.Adj x y}.toFinset
  let W := insert v <| insert w₁ <| insert w₂ (s ∪ t)
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : ∀ x, x ∈ X → 3 ≤ #(W.filter (¬ G.Adj x ·)) := by
    intro z hx
    by_contra! h
    obtain ⟨_, _, hW⟩ := hw.exists_isFiveWheelLike_succ_of_not_adj_le_two hc
      (by simpa [X] using hx) <| Nat.le_of_succ_le_succ h
    exact hm hW
  -- Since every vertex has at least one non-neighbor in `W` we now have the following upper bound
  -- `∑ w ∈ W, H.degree w ≤ #X * (#W - 3) + #Xᶜ * (#W - 1)`
  have bdW := sum_degree_le_of_le_not_adj dXle (fun y _ ↦ (hw.one_le_not_adj_of_cliqueFree hc) y)
  -- By the definition of `X`, any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : ∀ x, x ∈ Xᶜ → 1 ≤ #((s ∩ t).filter (¬ G.Adj x ·)) := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : ∃ y ∈ s ∩ t, ¬ G.Adj x y := by
      contrapose! hx
      rw [mem_compl, not_not, Set.mem_toFinset]
      exact hx _
    exact ⟨_, mem_filter.2 hy⟩
  -- So we also have an upper bound on the degree sum over `s ∩ t`
  -- `∑ w ∈ s ∩ t, H.degree w ≤ #Xᶜ * (#(s ∩ t) - 1) + #X * #(s ∩ t)`
  have bdX := sum_degree_le_of_le_not_adj xcle (fun x _ ↦ Nat.zero_le _)
  rw [compl_compl, tsub_zero, add_comm] at bdX
  rw [Nat.le_div_iff_mul_le <| Nat.add_pos_right _ zero_lt_three]
  have Wc : #W + k = 2 * r + 3 := hw.card_add_card_inter
  have w3 : 3 ≤ #W := two_lt_card.2 ⟨_, mem_insert_self .., _, by simp [W], _, by simp [W],
    hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩
  -- For simplicity we now split depending on whether or not `s ∩ t` is empty.
  by_cases hst : k = 0
  · -- `s ∩ t = ∅`
    -- In this case the degree sum over `W` implies the required upper bound on minimum degree
    rw [hst, add_zero] at Wc ⊢
    rw [← Wc, ← tsub_eq_of_eq_add Wc]
    have Xu : X = univ := by
      apply eq_univ_of_forall
      rw [← hw.card_inter, card_eq_zero] at hst
      intro x; simp [X, hst]
    rw [Xu, card_univ, compl_univ, card_empty, zero_mul, add_zero, mul_comm] at bdW
    apply bdW.trans'
    rw [card_eq_sum_ones, mul_sum, mul_one]
    exact sum_le_sum (fun i _ ↦ G.minDegree_le_degree i)
  · -- `s ∩ t ≠ ∅` so `1 ≤ k`
    -- In this case the sum of the degree sum over `W` with twice the degree sum over `s ∩ t`
    -- must be at least `G.minDegree * (#W + 2 * #(s ∩ t))` which implies the result
    have hap :  #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by omega
    calc
      minDegree G * (2 * r + k + 3) ≤ ∑ w ∈ W, G.degree w +  2 * ∑ w ∈ s ∩ t, G.degree w := by
        rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add]
        simp_rw [← hw.card_inter, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one]
        apply add_le_add <;> apply sum_le_sum <;> intro i _
        · exact minDegree_le_degree ..
        · exact mul_comm 2 _ ▸ (Nat.mul_le_mul_left _ <| G.minDegree_le_degree _)
      _ ≤ #X * (#W - 3) + #Xᶜ * (#W - 1) + 2 * (#X * k + #Xᶜ * (k - 1)) :=
          add_le_add bdW <| Nat.mul_le_mul_left _ (hw.card_inter ▸ bdX)
      _ = #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by ring_nf
      _ ≤ (2 * r + k) * ‖α‖ := by
        rw [hap, ← add_mul, card_compl, add_tsub_cancel_of_le (card_le_univ _), mul_comm]
        apply Nat.mul_le_mul_right
        rw [two_mul, ← add_assoc]
        apply Nat.add_le_add_right
        rw [tsub_add_eq_add_tsub w3, Wc, Nat.add_sub_cancel_right]

end IsFiveWheelLike

variable [DecidableEq α]

/-- **Andrasfái-Erdős-Sós**
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
    -- If  `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mono_left hle
    by_contra! hnotcol
    -- If `H` is complete-multipartite then, since `H` is `Kᵣ₊₃`-free, it is `r + 2`-colorable
    have hn : ¬ H.IsCompleteMultipartite := fun hc ↦ hnotcol <| hc.colorable_of_cliqueFree hmcf.1
    -- So `H` contains `Wᵣ₊₁,ₖ` but not `Wᵣ₊₁,ₖ₊₁`, for some `k ≤ r`
    obtain ⟨_, _, _, _, _, _, hw, hlt, hm⟩ :=
      exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite hmcf hn
    classical
    -- But the minimum degree of `G`, and hence of `H`, is too large for it to be `Wᵣ₊₁,ₖ₊₁`-free,
    -- a contradiction.
    have hD := hw.minDegree_le_of_cliqueFree_FiveWheelLikeFree_succ hmcf.1 <| hm _ <| lt_add_one _
    exact (hd.trans_le <| minDegree_le_minDegree hle).not_le
             <| hD.trans (kr_bound <| Nat.le_of_succ_le_succ <| hlt)

end AES
end SimpleGraph
