import Mathlib.Combinatorics.SimpleGraph.Brooks.PartialColoring
set_option linter.style.header false
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
open Finset


/-!
## Brooks' Theorem (for 3 ≤ k)
If `G : SimpleGraph α` and `Δ ≥ 3` is a natural number such that `G` is `Δ + 1`-clique free and
`∀ v, G.degree v ≤ Δ` then for any `s : Finset α` there exists a partial coloring of `s` that uses
at most `Δ` colors.

[Note below: `G.Greedy l` colors `[]` by `c v = 0` for all `v : α` and given `C := G.Greedy l` it
colors `(a :: l)` by `c v := ite (v = a) (greedy C a) (C v)` where `greedy C a` is the smallest
color not used by the neighbors of `a` in `C`. In particular it assigns `0` to any vertex not in `l`
and then uses the smallest color possible at each step.]

Proof: By strong induction on `#s`:

`ih : ∀ s, #s < n → ∃ C, G.PartialColoring s, ∀ v, C v < Δ`.

Now suppose we have `#s = n`.

If `∃ v ∈ s` such that `s ∩ Γ(v) < Δ` then apply `ih s.erase v` to obtain
`C : G.PartialColoring s.erase v`then use `C.insert a`
(the coloring of `s` given by greedily extending `C`) to complete the proof.

So wlog every vertex in `s` has exactly `Δ` neighbors in `s` (and hence no neighbors outside `s`).

Since `G` has no `Δ + 1`-clique so `s` contains no `Δ + 1`-clique.
Thus if `v₃ ∈ s` then `v₂` has neighbors `v₁` and `v₃` such that `v₁` and `v₃` are not neighbors.
Let `v₁v₂v₃⋯vᵣ₊₁` be a maximal path in `G`, so `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}.

We consider two cases:

1. We have `{v₁,…,vᵣ₊₁} = s`.
   Let `vⱼ ∈ Γ(v₂) \ {v₁,v₃}`. So `j ≥ 4`
   So `r + 1 = n`. Let `l = [v₁,v₃,v₄,…,vⱼ₋₁,vₙ,vₙ₋₁,…,vⱼ,v₂]` and check that `Greedy l` works.
   This is true since `c v₁ = c v₃ = 0` (they are not adjacent). Then `c vᵢ < Δ` for each
   `4 ≤ i ≤ j - 1` since when we color `vᵢ` its neighbor `vᵢ₊₁` is uncolored. The same is true for
   `n ≥ i ≥ j + 1` since `vᵢ` has a neighbor `vᵢ₋₁` that is uncolored.
   Finally `vⱼ` has uncolored neighbor `v₂` and finally `v₂` has two neigbors of the same color,
   namely `v₁` and `v₃`.

2. We have `{v₁,…,vᵣ₊₁} ≠ s`.
   In this case  let `j = min {i | vᵢ ∈ Γ(vᵣ₊₁)}`, so `j ≤ r - 1`.
   Let `t = s \ {vⱼ,…,vᵣ₊₁}` and `l` be the list given by `ih t`. Then `l` is a listing of `t` such
   that `G.Greedy l'` uses at most `Δ` colors.
   If there is no edge between `t` and `u := {vⱼ,…,vᵣ₊₁}` then we can apply `ih u` to get a listing
   `k` of `u` such that `G.Greedy k` uses at most `Δ` colors and `l ++ k` is the desired listing of
   `s`. Otherwise let `m := max {i | j ≤ i ≤ r + 1, Γ(vᵢ) ∩ t ≠ ∅}` and let `w ∈ Γ(vₘ) ∩ t`.
   Note that `m < r + 1` since `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}`. Note `vₘ₊₁` has no neighbor in `t` so we can
   set `c vₘ₊₁ = c w` [Problem : this is not greedy anymore!].
   Now let `k = [vₘ₊₂,…,vᵣ,vⱼ,…,vₘ₋₁,vₘ]`. Note that the only possible problem for coloring
   `k` greedily is at `vₘ`, but this is fine since `vₘ` has 2 neighbors of the same color, namely
   `w` and `vₘ₊₁`.
--------------------------------------------/

open PartialColoring Walk List

lemma Walk.IsCycle.support_rotate_tail_tail_eq [DecidableEq α] {u : α} {c : G.Walk u u} {d : G.Dart}
    (hc : c.IsCycle) (hd : d ∈ c.darts) :
    (c.rotate (c.dart_fst_mem_support_of_mem_darts hd)).tail.tail.support.toFinset =
      c.support.toFinset.erase d.toProd.2 := by
  ext x
  have hr := (c.dart_fst_mem_support_of_mem_darts hd)
  rw [Finset.mem_erase, mem_toFinset, mem_toFinset, hc.snd_eq_snd_of_rotate_fst_dart hd,
      (hc.rotate hr).mem_tail_tail_support_iff, mem_support_rotate_iff]

variable {k : ℕ} [Fintype α] [DecidableRel G.Adj] [DecidableEq α]

theorem BrooksPartial (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k)
    (s : Finset α) : ∃ C : G.PartialColoring s, C.IsPartialKColoring k := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | h n ih =>
  -- Case 0 : there is v ∈ s with d_s(v) < k, so we can extend a k-coloring of
  -- s.erase v greedily
  by_cases hd : ∃ v ∈ s, G.degreeOn (s.erase v) v < k
  · obtain ⟨v, hv, hlt⟩ := hd
    obtain ⟨C, hC⟩ := ih _ ((card_erase_lt_of_mem hv).trans_le hn.le) _ rfl
    use (C.insert v).copy (insert_erase hv), insert_of_lt hC ((C.extend_le_degreeOn _).trans_lt hlt)
  -- So all vertices in `s` have d_s(v) = k (and hence have no neighbors outside `s`)
  push_neg at hd
  replace hd : ∀ v ∈ s, G.degreeOn (s.erase v) v = k := fun v hv ↦ le_antisymm
        ((degreeOn_le_degree ..).trans (hbdd v)) <| hd _ hv
  have hbdd' : ∀ v, v ∈ s → G.degree v = k := fun v hv ↦ le_antisymm (hbdd v)
        <| hd v hv ▸ degreeOn_le_degree ..
  have hin : ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s := by
    by_contra! hf
    obtain ⟨v, hv, w, ha, hns⟩ := hf
    have := degreeOn_lt_degree ⟨by rwa [← mem_neighborFinset] at ha, hns⟩
    rw [← degreeOn_erase, hd _ hv] at this
    exact this.not_le (hbdd v)
  -- `s` is either Nonempty (main case) or empty (easy)
  by_cases hem : s.Nonempty
  · obtain ⟨v₂, hv₂⟩ := hem
    -- Since `G` is `k + 1`-cliquefree and `v₂` is a vertex in `s` (so has degree `k` in `s`)
    -- we know that `Γ(v₂).insert v₂` is not a clique
    have nc := hc <| insert v₂ (G.neighborFinset v₂ ∩ s)
    -- Since `Γ(v₂).insert v₂` is not a clique `v₂` has distinct non-adjacent neighbors
    -- in `s`, `v₁` and `v₃`
    have ⟨v₁, v₃, h1, h3, hne, hnadj⟩ : ∃ v₁ v₃, v₁ ∈ G.neighborFinset v₂ ∩ s ∧
        v₃ ∈ G.neighborFinset v₂ ∩ s ∧ v₁ ≠ v₃ ∧ ¬ G.Adj v₁ v₃ := by
      contrapose! nc
      apply IsNClique.insert
        ⟨fun _ ha _ hb hne ↦ nc _ _ ha hb hne, by rw [← hd _ hv₂, degreeOn_erase]⟩
      intro b hb; rw [mem_inter, mem_neighborFinset] at hb
      exact hb.1
    -- Since `v₃` has degree at least 3 so it has another neighbor `v₄ ≠ v₂`
    have ⟨v₄, h34, h4⟩ := G.exists_adj_ne_of_one_lt_degree v₃
                  (Nat.lt_of_succ_lt <| hk.trans (hbdd' _ (mem_inter.1 h3).2).symm.le) v₂
    rw [mem_inter, mem_neighborFinset] at h1 h3
    rw [adj_comm] at h3
    -- We can build the path v₁v₂v₃v₄`
    let v41 := ((Walk.cons h1.1 nil).cons h3.1).cons h34.symm
    have h41 : v41.IsPath := by
      rw [cons_isPath_iff]
      simpa using ⟨⟨h1.1.ne, h3.1.ne, hne.symm⟩, h34.symm.ne, h4, fun hf ↦ hnadj (hf ▸ h34.symm)⟩
    have v41sup : v41.support = [v₄, v₃, v₂, v₁] := by
      rw [support_cons, support_cons, support_cons, support_nil]
    have mv41 : ∀ y, y ∈ v41.support → y = v₄ ∨ y = v₃ ∨ y = v₂ ∨ y = v₁ := by simp [v41sup]
    have v41s : ∀ y, y ∈ v41.support → y ∈ s := by
      intro y hy
      cases mv41 y hy with
      | inl h => exact h ▸ (hin _ h3.2 _ h34)
      | inr h => cases h with
                | inl h => exact h ▸ h3.2
                | inr h => cases h with
                           | inl h => exact h ▸ hv₂
                           | inr h => exact h ▸ h1.2
    -- Now extend `v₁v₂v₃v₄` to a maximal path in `s` i.e. a path `v₁ ⋯ vᵣ`
    -- with all neighbors of `vᵣ` in the path
    obtain ⟨vᵣ, q, hq, hss, hmax⟩ : ∃ vᵣ, ∃ q : G.Walk vᵣ v₄, (q.append v41).IsPath ∧
      (∀ y, y ∈ (q.append v41).support → y ∈ s) ∧
        ∀ y, G.Adj vᵣ y → y ∈ ((q.append v41)).support := by
      obtain ⟨vᵣ, q, hq, hs, hnb⟩ := exists_maximal_path_subset s h41 v41s
      refine ⟨vᵣ, q, hq, hs,fun x hx ↦ ?_⟩
      have := (hbdd vᵣ).trans (hd vᵣ (hs _ (start_mem_support ..))).symm.le
      rw [degreeOn_erase, degree_le_degreeOn_iff] at this
      exact hnb x hx <| this <| (mem_neighborFinset ..).2 hx
    have hdisj2 := (append_isPath_iff.1 hq).2.2
    -- either this path is the whole of `s` or it is a proper subset
    by_cases hr : ((q.append v41)).support.toFinset = s
    · --Main Case 1 the path is all of s
      simp_rw [support_append, v41sup, List.tail, toFinset_append, toFinset_cons, toFinset_nil,
                insert_emptyc_eq] at hr
      obtain ⟨vⱼ, hj⟩ := G.exists_adj_ne_of_two_lt_degree v₂ (hk.trans (hbdd' _ hv₂).symm.le) v₁ v₃
      have hj : G.Adj v₂ vⱼ ∧ vⱼ ≠ v₁ ∧ vⱼ ≠ v₃ ∧ vⱼ ∈ s := ⟨hj.1, hj.2.1, hj.2.2, hin _ hv₂ _ hj.1⟩
      have h1q := fun hf ↦ hdisj2 hf ((mem_cons_of_mem _ <| mem_cons_of_mem _ <| mem_cons_self ..))
      have h2q := fun hf ↦ hdisj2 hf (mem_cons_of_mem _ <| mem_cons_self ..)
      have h3q := fun hf ↦ hdisj2 hf (mem_cons_self ..)
      have hj123: vⱼ ∉ ({v₃ , v₂, v₁} : Finset α) := by simpa using ⟨hj.2.2.1, hj.1.symm.ne, hj.2.1⟩
      have hvjq : vⱼ ∈ q.support := by
        cases (mem_union.1 (hr ▸ hj.2.2.2)) with
        | inl h => exact mem_toFinset.1 h
        | inr h => exact (hj123 h).elim
      obtain ⟨C, hC⟩ := Brooks1_exists hk hbdd hq.of_append_left hvjq hj.1.symm h1.1 h3.1.symm hne
                             hnadj h1q h2q h3q
      exact ⟨C.copy hr, hC⟩
    · -- Main case 2 the path is a proper subset of s
      -- in which case we can build a cycle `c` from `vᵣ` such that all the neighbors
      -- of `vᵣ` lie in `c`
      have hssf := Finset.ssubset_iff_subset_ne.2 ⟨fun y hy ↦ hss _ <| mem_toFinset.1 hy, hr⟩
      have h1 := Nat.lt_of_succ_lt <| hk.trans (hbdd' _ <| hss _ <| start_mem_support ..).symm.le
      let p := (q.append v41).reverse
      let S := {x | G.Adj vᵣ x ∧ x ≠ p.penultimate}
      obtain ⟨y, hy⟩ : ∃ y, y ∈ S := G.exists_adj_ne_of_one_lt_degree vᵣ h1 p.penultimate
      have hmaxp : ∀ x, G.Adj vᵣ x → x ∈ p.support := by
        simp_rw [p, support_reverse, mem_reverse]; exact hmax
      obtain ⟨m, hm⟩ := exists_getVert_first p hy (fun x hx ↦ hmaxp x hx.1)
      let c := (p.drop m).cons (hm.1.1)
      have hcy := hq.reverse.cons_drop_isCycle hm.1.1 hm.1.2
      have hmlt : m < p.length := by
        by_contra!
        exact G.loopless _ <| (p.getVert_of_length_le this) ▸ hm.1.1
      have hcym : ∀ x, G.Adj vᵣ x → x ∈ c.support := by
        intro x hx; rw [support_cons]
        by_cases hxpen : x = p.penultimate
        · exact hxpen ▸ mem_cons_of_mem _ (mem_support_drop _ (by omega))
        · exact mem_cons_of_mem _ (hm.2 _ ⟨hx, hxpen⟩)
      have hsub : c.support.toFinset ⊂ s := by
        apply Finset.ssubset_of_subset_of_ssubset _ hssf
        intro y hy
        rw [mem_toFinset, support_cons] at *
        cases hy with
        | head _ => exact start_mem_support ..
        | tail _ hy =>
          have := (support_drop_subset _ _) hy
          rwa [support_reverse, mem_reverse] at this
      -- `c` is not empty
      -- so we will be able to color `c` and `s \ c` by induction if needed
      have hsdcard : #(s \ c.support.toFinset) < n := by
        rw [card_sdiff hsub.1]
        apply hn.le.trans_lt'
        rw [Nat.sub_lt_iff_lt_add (card_le_card hsub.1)]
        exact Nat.lt_add_of_pos_left <| card_pos.2 ⟨_, mem_toFinset.2 c.start_mem_support⟩
      -- Two subcases either `c` has a neighbor in `s \ c` or not
      by_cases hnbc : ∃ x, x ∈ c.support ∧ ∃ y, y ∈ s \ c.support.toFinset ∧ G.Adj x y
      · obtain ⟨x, hx, y, hy, had⟩ := hnbc
        --`x ∈ c` has a neighbor `y ∈ s \ c` (but `vᵣ ∈ c` has no neighbors in `s \ c`)
        -- so there is a first dart `d = (d₁, d₂)` in `c` such that `d₁` is adjacent
        -- to something `s \ c` and `d₂` is not
        have rS : vᵣ ∉ {a | ∃ b ∈ s \ c.support.toFinset, G.Adj a b} :=
          fun ⟨ _, hy , had⟩ ↦ (mem_sdiff.1 hy).2 <| mem_toFinset.2 <| hcym _ had
        obtain ⟨d, hd, ⟨y, hy1, hd1⟩, hd2⟩ := exists_boundary_dart_of_closed c _
                      (Set.mem_setOf.2 ⟨_, hy, had⟩) rS hx (start_mem_support ..)
        have d2 : ∀ b ∈ s \ c.support.toFinset, ¬ G.Adj d.toProd.2 b := by
          contrapose! hd2; exact hd2
        -- We color `s \ c` by induction
        obtain ⟨C₁, hC₁⟩ := ih _ hsdcard _ rfl
        -- we then extend this coloring to `d₂` by coloring `d₂` with the color of `y`
        -- the neighbor of `d₁` (so now `d₁` is a vertex on `c` that has two neigbors
        -- colored with the same color)
        let C₂ := C₁.insertNotAdj d2 y
        have hC₂ := C₁.lt_of_insertNotAdj_lt d2 y hC₁
        let hr := (c.dart_fst_mem_support_of_mem_darts hd)
        -- we take the path given by removing `d₂` from `c` (we do this by rotating
        -- `c` to start at `d₁` and then removing its last two darts)
        let p := (c.rotate hr).tail.tail
        have hp : p.IsPath := (hcy.rotate hr).isPath_tail.tail
        have hne : d.toProd.2 ≠ y := by
          intro hf; subst_vars
          exact (mem_sdiff.1 hy1).2 <| mem_toFinset.2 (c.dart_snd_mem_support_of_mem_darts hd)
        -- We will color the vertices in `p` greedily in reverse order, so ending with `d₁`
        have hd2 := mem_toFinset.2 (c.dart_snd_mem_support_of_mem_darts hd)
        have hsdc := sdiff_union_of_subset hsub.1
        have heq : (insert d.toProd.2 (s \ c.support.toFinset)
                      ∪ p.reverse.support.toFinset) = s := by
          rwa [support_reverse, toFinset_reverse, hcy.support_rotate_tail_tail_eq hd, insert_union,
           ← erase_eq_of_not_mem (not_mem_sdiff_of_mem_right hd2), ← erase_union_distrib,
            insert_erase (hsdc.symm ▸ (hsub.1 hd2))]
        have hps : p.support.toFinset ⊆ c.support.toFinset := by
          intro x hx
          rw [mem_toFinset] at *
          exact (mem_support_rotate_iff hr).1 (support_drop_subset _ _ (support_drop_subset _ _ hx))
        have hdisj : Disjoint (insert d.toProd.2 (s \ c.support.toFinset))
          p.reverse.support.toFinset := by
          rw [support_reverse, toFinset_reverse]
          apply disjoint_insert_left.2
          refine ⟨?_, disjoint_of_subset_right hps sdiff_disjoint⟩
          rw [mem_toFinset, hcy.snd_eq_snd_of_rotate_fst_dart hd]
          exact (hcy.rotate hr).snd_not_mem_tail_tail_support
        -- We know that when extending a coloring greedily along a path whose end point
        -- already has two neighbors colored with the same color we never need to use
        -- more that `k` colors along the path.
        exact ⟨(C₂.Greedy p.reverse.support).copy heq, C₂.Greedy_of_path_notInj hbdd hp.reverse hC₂
         (mem_insert_self ..) (mem_insert_of_mem hy1) d.adj hd1 hne (C₁.eq_ofinsertNotAdj d2) hdisj⟩
      · -- The cycle `c` has no edges into `s \ c` and so we can now color
        -- `c` and `s \ c` by induction and then join the colorings together
        obtain ⟨C₁, hC₁⟩ := ih _ ((card_lt_card hsub).trans_le hn.le)  _ rfl
        obtain ⟨C₂, hC₂⟩ := ih _ hsdcard _ rfl
        exact ⟨(C₁.join C₂ (by simpa using hnbc)).copy (union_sdiff_of_subset hsub.1),
          copy_isK (C₁.join_isK_of_isK hC₁ hC₂)⟩
  · -- `s` is empty so easy to `k`-color
    exact ⟨G.partialColoringOfEmpty.copy (not_nonempty_iff_eq_empty.1 hem).symm,
      fun v ↦ by simpa using Nat.zero_lt_of_lt hk⟩

theorem Brooks_three_le (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k) :
    G.Colorable k :=
  let ⟨C, isK⟩ := BrooksPartial hk hc hbdd (univ : Finset α)
  ⟨C.toKColoring isK⟩

end SimpleGraph
