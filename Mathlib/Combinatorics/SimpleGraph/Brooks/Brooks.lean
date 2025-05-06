/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Brooks.Greedy
import Mathlib.Combinatorics.SimpleGraph.Brooks.OddCycles

/-!
## Brooks' Theorem (for 3 ≤ k)
If `G : SimpleGraph α` and `k ≥ 3` is a natural number such that `G` is `k + 1`-clique free and
`∀ v, G.degree v ≤ k` then for any `s : Finset α` there exists a partial coloring of `s` that uses
at most `k` colors.

Proof: By strong induction on `#s`:

`ih : ∀ m < n, ∀ (s : Finset α), #s = m → G.PartColorable k ↑s`.

Now suppose we have `#s = n`.

If `∃ v ∈ s` such that `s ∩ Γ(v) < k` then apply `ih s.erase v` to obtain
`C : G.PartColoring s.erase v`then use `C.insert a`
(the coloring of `s` given by greedily extending `C`) to complete the proof.

So wlog every vertex in `s` has exactly `k` neighbors in `s` (and hence no neighbors outside `s`).

Since `G` has no `k + 1`-clique so `s` contains no `k + 1`-clique.
Thus if `v₃ ∈ s` then `v₂` has neighbors `v₁` and `v₃` such that `v₁` and `v₃` are not neighbors.
Let `v₁v₂v₃⋯vᵣ₊₁` be a maximal path in `G`, so `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}.

We consider two cases:

1. We have `{v₁,…,vᵣ₊₁} = s`.
   Let `vⱼ ∈ Γ(v₂) \ {v₁,v₃}`. So `j ≥ 4`
   So `r + 1 = n`. Let `l = [v₁,v₃,v₄,…,vⱼ₋₁,vₙ,vₙ₋₁,…,vⱼ,v₂]` and check that `Greedy l` works.
   This is true since `c v₁ = c v₃ = 0` (they are not adjacent). Then `c vᵢ < k` for each
   `4 ≤ i ≤ j - 1` since when we color `vᵢ` its neighbor `vᵢ₊₁` is uncolored. The same is true for
   `n ≥ i ≥ j + 1` since `vᵢ` has a neighbor `vᵢ₋₁` that is uncolored.
   Finally `vⱼ` has uncolored neighbor `v₂` and finally `v₂` has two neigbors of the same color,
   namely `v₁` and `v₃`.

2. We have `{v₁,…,vᵣ₊₁} ≠ s`.
   In this case  let `j = min {i | vᵢ ∈ Γ(vᵣ₊₁)}`, so `j ≤ r - 1`.
   Let `t = s \ {vⱼ,…,vᵣ₊₁}` and `l` be the list given by `ih t`. Then `l` is a listing of `t` such
   that `G.Greedy l'` uses at most `k` colors.
   If there is no edge between `t` and `u := {vⱼ,…,vᵣ₊₁}` then we can apply `ih u` to get a listing
   `k` of `u` such that `G.Greedy k` uses at most `k` colors and `l ++ k` is the desired listing of
   `s`. Otherwise let `m := max {i | j ≤ i ≤ r + 1, Γ(vᵢ) ∩ t ≠ ∅}` and let `w ∈ Γ(vₘ) ∩ t`.
   Note that `m < r + 1` since `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}`. Note `vₘ₊₁` has no neighbor in `t` so we can
   set `c vₘ₊₁ = c w` [Problem : this is not greedy anymore!].
   Now let `k = [vₘ₊₂,…,vᵣ,vⱼ,…,vₘ₋₁,vₘ]`. Note that the only possible problem for coloring
   `k` greedily is at `vₘ`, but this is fine since `vₘ` has 2 neighbors of the same color, namely
   `w` and `vₘ₊₁`.

--------------------------------------------/
namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

open List Walk Finset

/-- If a path `q : G.Walk u v` is contained in a Finset `s` then we can extend it to a path `p ++ q`
contained in `s`, where `p : G.Walk x u` and `x` has no neighbors in `s` outside of `p ++ q`. -/
lemma Walk.exists_maximal_path_subset {u v : α} {q : G.Walk u v} (s : Finset α) (hq : q.IsPath)
    (hs : ∀ y , y ∈ q.support → y ∈ s) :
    ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (∀ y, y ∈ (p.append q).support → y ∈ s) ∧
    ∀ y, G.Adj x y → y ∈ s → y ∈ (p.append q).support := by
  classical
  by_contra! hf
  have : ∀ n, ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (∀ x, x ∈ (p.append q).support → x ∈ s) ∧
    n ≤ (p.append q).length := by
    intro n
    induction n with
    | zero => exact ⟨u, .nil, by simpa using ⟨hq, hs⟩⟩
    | succ n ih =>
      obtain ⟨x, p, hp, hs, hc⟩ := ih
      obtain ⟨y, hy⟩ := hf x p hp hs
      exact ⟨y, p.cons hy.1.symm, by aesop⟩
  obtain ⟨_, _, hp, hc1, hc2⟩ := this s.card
  simp_rw [← List.mem_toFinset] at hc1
  have := length_support _ ▸ (List.toFinset_card_of_nodup hp.2) ▸ (card_le_card hc1)
  exact hc2.not_lt this

lemma Walk.IsCycle.support_rotate_tail_tail_eq [DecidableEq α] {u : α} {c : G.Walk u u} {d : G.Dart}
    (hc : c.IsCycle) (hd : d ∈ c.darts) :
    (c.rotate (c.dart_fst_mem_support_of_mem_darts hd)).tail.tail.support.toFinset =
      c.support.toFinset.erase d.toProd.2 := by
  ext x
  have hr := (c.dart_fst_mem_support_of_mem_darts hd)
  rw [mem_erase, List.mem_toFinset, List.mem_toFinset, hc.snd_eq_snd_of_rotate_fst_dart hd,
      (hc.rotate hr).mem_tail_tail_support_iff, mem_support_rotate_iff]

open PartColoring

variable {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄} {k : ℕ}

lemma Brooks1 [DecidableRel G.Adj] [LocallyFinite G] [DecidableEq α] (hk : 3 ≤ k)
    (hbd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support) (hj2 : G.Adj xⱼ x₂)
    (h21 : G.Adj x₂ x₁) (h23 : G.Adj x₂ x₃) (hne : x₁ ≠ x₃) (h13 : ¬ G.Adj x₁ x₃)
    (h1 : x₁ ∉ p.support) (h2 : x₂ ∉ p.support) (h3 : x₃ ∉ p.support) :
    G.PartColorable k ({a | a ∈ p.support} ∪ {x₃, x₂, x₁}) := by
  have htp := ((concat_isPath_iff _ hj2).2 ⟨hp.takeUntil hj,
              fun a ↦ h2 ((p.support_takeUntil_subset hj) a)⟩).reverse
  have hd1 : Disjoint {x₁, x₃} {a | a ∈ (p.dropUntil xⱼ hj).support} := by
    simp only [Set.disjoint_insert_left, Set.mem_setOf_eq, Set.disjoint_singleton_left]
    exact ⟨fun h ↦ h1 (p.support_dropUntil_subset hj h) ,
          fun h ↦ h3 (p.support_dropUntil_subset hj h)⟩
  let C₀ := (G.partColoringOfNotAdj h13 (β := Fin k) ⟨0, show 0 < k by omega⟩)
  let C₁ := C₀.of_tail_path (hp.dropUntil hj) (fun _ _ ↦ ((Fintype.card_fin _).symm ▸ (hbd _))) hd1
  have hj213 : C₁ x₁ = C₁ x₃ := by
    have := (C₀.of_tail_path_extends (hp.dropUntil hj)
            (fun _ _ ↦ (Fintype.card_fin _).symm ▸ (hbd _)) hd1)
    rw [this.2 (by simp), this.2 (by simp)]; rfl
  exact ⟨(C₁.of_path_not_inj htp (fun _ _ ↦ (Fintype.card_fin _).symm ▸ (hbd _)) (by
    apply Set.disjoint_union_left.2
    simp only [Walk.reverse_concat, support_cons, support_reverse, List.mem_cons, List.mem_reverse,
      Set.disjoint_insert_left, Set.mem_setOf_eq, not_or, Set.disjoint_singleton_left]
    refine ⟨⟨⟨h21.symm.ne, fun a ↦ h1 ((support_takeUntil_subset p hj) a)⟩, ⟨h23.symm.ne, fun a ↦ h3
      ((support_takeUntil_subset p hj) a)⟩⟩,?_⟩
    apply Set.disjoint_right.2
    rintro a (rfl | ha)
    · exact fun h ↦ h2 (p.support_dropUntil_subset hj <| List.mem_of_mem_tail h)
    · rw [← take_spec p hj, append_isPath_iff] at hp; exact fun h ↦ hp.2.2 ha h)
    (by simp) (by simp) h21 h23 hne hj213).copy ((by
    rw [Set.pair_comm, support_reverse, support_concat]
    nth_rw 3 [← take_spec p hj]
    rw [support_append, List.concat_eq_append, List.reverse_append, List.reverse_cons]
    ext; aesop))⟩

open List
theorem BrooksPart [LocallyFinite G] {k : ℕ} (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1))
    (hbd : ∀ v, G.degree v ≤ k) (s : Finset α) : G.PartColorable k s := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | h n ih =>
  -- Case 0 : there is `v ∈ s` with `G.degreeInduce s v < k`, so we can extend a `k` - coloring of
  -- `s.erase v` greedily
  classical
  by_cases hd : ∃ v ∈ s, G.degreeInduce s v < k
  · obtain ⟨v, hv, hlt⟩ := hd
    obtain ⟨C⟩ := ih _ ((card_erase_lt_of_mem hv).trans_le hn.le) _ rfl
    exact ⟨(C.greedy v (C.nonempty_of_degreeInduce_lt _
      (by simpa [hv] using hlt))).copy (by simp [hv])⟩
  -- So all vertices in `s` have `G.degreeInduce s v = k` (and hence have no neighbors outside `s`)
  push_neg at hd
  replace hd : ∀ v ∈ s, G.degreeInduce s v = k := fun v hv ↦ le_antisymm
        ((degreeInduce_le_degree ..).trans (hbd v)) <| hd _ hv
  have hbd' : ∀ v, v ∈ s → G.degree v = k := fun v hv ↦ le_antisymm (hbd v)
        <| hd v hv ▸ degreeInduce_le_degree ..
  have hin : ∀ {v}, v ∈ s → ∀ {w}, G.Adj v w → w ∈ s := by
    by_contra! hf
    obtain ⟨v, hv, w, ha, hns⟩ := hf
    have : G.degreeInduce s v < G.degree v := G.degreeInduce_lt_degree ⟨ha, hns⟩
    rw [hd _ hv] at this
    exact this.not_le (hbd v)
  -- `s` is either Nonempty (main case) or empty (easy)
  by_cases hem : ¬ s.Nonempty
  · -- `s` is empty so easy to `k`-color
    exact ⟨fun _ ↦ ⟨0, by omega⟩, by simp_all⟩
  obtain ⟨v₂, hv₂⟩ := by rwa [not_not] at hem
  -- Since `G` is `k + 1`-cliquefree and `v₂` is a vertex in `s` (so has degree `k` in `s`)
  -- we know that `Γ(v₂).insert v₂` is not a clique
  have nc := hc <| insert v₂ (G.neighborFinset v₂ ∩ s)
  -- Since `Γ(v₂).insert v₂` is not a clique `v₂` has distinct non-adjacent neighbors
  -- in `s`, `v₁` and `v₃`
  have ⟨v₁, v₃, h1, h3, hne, nadj⟩ : ∃ v₁ v₃, v₁ ∈ G.neighborFinset v₂ ∩ s ∧
      v₃ ∈ G.neighborFinset v₂ ∩ s ∧ v₁ ≠ v₃ ∧ ¬ G.Adj v₁ v₃ := by
    contrapose! nc
    apply IsNClique.insert
      ⟨fun _ ha _ hb hne ↦ nc _ _ ha hb hne, by rw [← hd _ hv₂]; congr; ext; simp [hv₂, and_comm]⟩
    intro b hb; rw [mem_inter, mem_neighborFinset] at hb
    exact hb.1
  -- Since `v₃` has degree at least 3 so it has another neighbor `v₄ ≠ v₂`
  have ⟨v₄, h34, h4⟩ := G.exists_adj_ne_of_one_lt_degree v₃
                (Nat.lt_of_succ_lt <| hk.trans (hbd' _ (mem_inter.1 h3).2).symm.le) v₂
  rw [mem_inter, mem_neighborFinset] at h1 h3
  rw [adj_comm] at h3
  -- We can build the path v₁v₂v₃v₄`
  let v41 := ((Walk.cons h1.1 nil).cons h3.1).cons h34.symm
  have h41 : v41.IsPath := by
    rw [cons_isPath_iff]
    simpa using ⟨⟨h1.1.ne, h3.1.ne, hne.symm⟩, h34.symm.ne, h4, fun hf ↦ nadj (hf ▸ h34.symm)⟩
  have v41sup : v41.support = [v₄, v₃, v₂, v₁] := rfl
  have mv41 : ∀ y, y ∈ v41.support → y = v₄ ∨ y = v₃ ∨ y = v₂ ∨ y = v₁ := by simp [v41sup]
  have v41s : ∀ y, y ∈ v41.support → y ∈ s := by
    intro y hy
    obtain (rfl | rfl | rfl | rfl) := mv41 y hy
    · exact hin h3.2 h34
    · exact h3.2
    · exact hv₂
    · exact h1.2
  -- Now extend `v₁v₂v₃v₄` to a maximal path in `s` i.e. a path `v₁ ⋯ vᵣ`
  -- with all neighbors of `vᵣ` in the path
  obtain ⟨vᵣ, q, hq, hss, hmax⟩ : ∃ vᵣ, ∃ q : G.Walk vᵣ v₄, (q.append v41).IsPath ∧
    (∀ y, y ∈ (q.append v41).support → y ∈ s) ∧
      ∀ y, G.Adj vᵣ y → y ∈ ((q.append v41)).support := by
    obtain ⟨vᵣ, q, hq, hs, hnb⟩ := exists_maximal_path_subset s h41 v41s
    refine ⟨vᵣ, q, hq, hs,fun x hx ↦ ?_⟩
    have := G.neighborSet_subset_of_degree_le_degreeInduce <|
      (hbd vᵣ).trans (hd vᵣ (hs _ (start_mem_support ..))).symm.le
    exact hnb x hx <| this <| (mem_neighborSet ..).2 hx
  have hdisj2 := (append_isPath_iff.1 hq).2.2
  -- either this path is the whole of `s` or it is a proper subset
  by_cases hr : {a | a ∈ ((q.append v41)).support} = s
  · --Main Case 1 the path is all of s
    simp_rw [support_append, v41sup, List.tail, List.mem_append] at hr
    obtain ⟨vⱼ, hj⟩ := G.exists_adj_ne_of_two_lt_degree v₂ (hk.trans (hbd' _ hv₂).symm.le) v₁ v₃
    have hj : G.Adj v₂ vⱼ ∧ vⱼ ≠ v₁ ∧ vⱼ ≠ v₃ ∧ vⱼ ∈ s := ⟨hj.1, hj.2.1, hj.2.2, hin hv₂ hj.1⟩
    have h1q := fun hf ↦ hdisj2 hf
      ((List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_self ..))
    have h2q := fun hf ↦ hdisj2 hf (List.mem_cons_of_mem _ <| List.mem_cons_self ..)
    have h3q := fun hf ↦ hdisj2 hf (List.mem_cons_self ..)
    have hj123: vⱼ ∉ [v₃ , v₂, v₁] := by simpa using ⟨hj.2.2.1, hj.1.symm.ne, hj.2.1⟩
    have hjq : vⱼ ∈ q.support := by
      rw [Set.ext_iff] at hr
      apply ((hr vⱼ).2 hj.2.2.2).resolve_right hj123
    change {a | a ∈ q.support} ∪ {a | a ∈ [v₃,v₂,v₁]} = s at hr
    have : {a | a ∈ [v₃,v₂,v₁]} = {v₃, v₂, v₁} := by ext; simp
    rw [this] at hr
    simp_rw [← hr]
    simpa using Brooks1 hk hbd hq.of_append_left hjq hj.1.symm h1.1 h3.1.symm hne nadj h1q h2q h3q
  · -- Main case 2 the path is a proper subset of s
    -- in which case we can build a cycle `c` from `vᵣ` such that all the neighbors
    -- of `vᵣ` lie in `c`
    have hr' : (q.append v41).support.toFinset ≠ s := by
      rw [← List.coe_toFinset] at hr; norm_cast at hr
    have hssf := Finset.ssubset_iff_subset_ne.2 ⟨fun y hy ↦ hss _ <| List.mem_toFinset.1 hy, hr'⟩
    have h1 := Nat.lt_of_succ_lt <| hk.trans (hbd' _ <| hss _ <| start_mem_support ..).symm.le
    let p := (q.append v41).reverse
    let S := {x | G.Adj vᵣ x ∧ x ≠ p.penultimate}
    obtain ⟨y, hy⟩ : ∃ y, y ∈ S := G.exists_adj_ne_of_one_lt_degree vᵣ h1 p.penultimate
    have hmaxp : ∀ x, G.Adj vᵣ x → x ∈ p.support := by
      simp_rw [p, support_reverse, List.mem_reverse]; exact hmax
    obtain ⟨m, hm⟩ := exists_getVert_first p hy (fun x hx ↦ hmaxp x hx.1)
    let c := (p.drop m).cons (hm.1.1)
    have hcy := hq.reverse.cons_drop_isCycle hm.1.1 hm.1.2
    have hmlt : m < p.length := by
      by_contra!
      exact G.loopless _ <| (p.getVert_of_length_le this) ▸ hm.1.1
    have hcym : ∀ x, G.Adj vᵣ x → x ∈ c.support := by
      intro x hx; rw [support_cons]
      by_cases hxpen : x = p.penultimate
      · exact hxpen ▸ List.mem_cons_of_mem _ (mem_support_drop _ (by omega))
      · exact List.mem_cons_of_mem _ (hm.2 _ ⟨hx, hxpen⟩)
    have hsub : c.support.toFinset ⊂ s := by
      apply Finset.ssubset_of_subset_of_ssubset _ hssf
      intro y hy
      rw [List.mem_toFinset, support_cons] at *
      obtain ( rfl | hy ) := List.mem_cons.1 hy
      · exact start_mem_support ..
      · have := (support_drop_subset _ _) hy
        rwa [support_reverse, List.mem_reverse] at this
    -- `c` is not empty
    -- so we will be able to color `c` and `s \ c` by induction if needed
    have hsdcard : #(s \ c.support.toFinset) < n := by
      rw [card_sdiff hsub.1]
      apply hn.le.trans_lt'
      rw [Nat.sub_lt_iff_lt_add (card_le_card hsub.1)]
      exact Nat.lt_add_of_pos_left <| card_pos.2 ⟨_, List.mem_toFinset.2 c.start_mem_support⟩
    -- Two subcases either `c` has a neighbor in `s \ c` or not
    by_cases hnbc : ∃ x, x ∈ c.support ∧ ∃ y, y ∈ s \ c.support.toFinset ∧ G.Adj x y
    · obtain ⟨x, hx, y, hy, had⟩ := hnbc
      -- `x ∈ c` has a neighbor `y ∈ s \ c` (but `vᵣ ∈ c` has no neighbors in `s \ c`)
      -- so there is a first dart `d = (d₁, d₂)` in `c` such that `d₁` is adjacent
      -- to something `s \ c` and `d₂` is not
      have rS : vᵣ ∉ {a | ∃ b ∈ s \ c.support.toFinset, G.Adj a b} :=
        fun ⟨_, hy , had⟩ ↦ (mem_sdiff.1 hy).2 <| List.mem_toFinset.2 <| hcym _ had
      obtain ⟨d, hd, ⟨y, hy1, hd1⟩, hd2⟩ := exists_boundary_dart_of_closed c _
                    (Set.mem_setOf.2 ⟨_, hy, had⟩) rS hx (start_mem_support ..)
      have d2 : ∀ b ∈ s \ c.support.toFinset, ¬ G.Adj d.toProd.2 b := by
        contrapose! hd2; exact hd2
      -- We color `s \ c` by induction
      obtain ⟨C₁⟩ := ih _ hsdcard _ rfl
      -- we then extend this coloring to `d₂` by coloring `d₂` with the color of `y`
      -- the neighbor of `d₁` (so now `d₁` is a vertex on `c` that has two neigbors
      -- colored with the same color)
      let C₂ := C₁.insert d.toProd.2 (c := (C₁ y)) (fun v h h' ↦ (d2 _ (by simpa using h) h').elim)
      let hr := (c.dart_fst_mem_support_of_mem_darts hd)
      -- we take the path given by removing `d₂` from `c` (we do this by rotating
      -- `c` to start at `d₁` and then removing its last two darts)
      let p := (c.rotate hr).tail.tail
      have hp : p.IsPath := (hcy.rotate hr).isPath_tail.tail
      have hne : d.toProd.2 ≠ y := by
        intro hf; subst_vars
        exact (mem_sdiff.1 hy1).2 <| List.mem_toFinset.2 (c.dart_snd_mem_support_of_mem_darts hd)
      -- We will color the vertices in `p` greedily in reverse order, so ending with `d₁`
      have hd2 := List.mem_toFinset.2 (c.dart_snd_mem_support_of_mem_darts hd)
      have hsdc := sdiff_union_of_subset hsub.1
      have heq : (insert d.toProd.2 (s \ c.support.toFinset)
                    ∪ p.reverse.support.toFinset) = s := by
        rwa [support_reverse, List.toFinset_reverse, hcy.support_rotate_tail_tail_eq hd,
          insert_union, ← erase_eq_of_not_mem (not_mem_sdiff_of_mem_right hd2),
          ← erase_union_distrib, insert_erase (hsdc.symm ▸ (hsub.1 hd2))]
      have hps : p.support.toFinset ⊆ c.support.toFinset := by
        rw [List.toFinset_subset]
        intro x hx
        exact (mem_support_rotate_iff hr).1 (support_drop_subset _ _ (support_drop_subset _ _ hx))
      have hdisj : Disjoint (insert d.toProd.2 (s \ c.support.toFinset))
        p.reverse.support.toFinset := by
        rw [support_reverse, List.toFinset_reverse]
        apply disjoint_insert_left.2
        refine ⟨?_, disjoint_of_subset_right hps sdiff_disjoint⟩
        rw [List.mem_toFinset, hcy.snd_eq_snd_of_rotate_fst_dart hd]
        exact (hcy.rotate hr).snd_not_mem_tail_tail_support
      rw [← disjoint_coe, List.coe_toFinset, coe_insert] at hdisj
      -- When extending a coloring greedily along a path whose end point
      -- already has two neighbors colored with the same color we never need to use
      -- more that `k` colors along the path.
      have hex : C₂ d.toProd.2 = C₂ y := by
        rw [C₁.insert_def , if_pos rfl, C₁.insert_def, if_neg hne.symm]
      exact ⟨(C₂.of_path_not_inj hp.reverse (fun v hv ↦ (Fintype.card_fin _).symm ▸ (hbd v)) hdisj
        (by simp) (by norm_cast; apply mem_insert_of_mem hy1) d.adj hd1 hne hex).copy
        (by rw [← List.coe_toFinset]; nth_rw 2 [← heq]; norm_cast)⟩
    · -- The cycle `c` has no edges into `s \ c` and so we can now color
      -- `c` and `s \ c` by induction and then join the colorings together
      push_neg at hnbc
      let ⟨C₁⟩ := ih _ ((card_lt_card hsub).trans_le hn.le)  _ rfl
      let ⟨C₂⟩ := ih _ hsdcard _ rfl
      exact ⟨(C₁.union C₂ (fun _ _ hv hw had ↦
        ((hnbc _ (by simpa using hv) _ (by simpa using hw)) had).elim)).copy (by
          ext; simp only [List.coe_toFinset, coe_sdiff, Set.union_diff_self, Set.mem_union,
            Set.mem_setOf_eq, mem_coe, or_iff_right_iff_imp]
          exact fun hc ↦ hsub.1 <| List.mem_toFinset.mpr hc)⟩

theorem colorable_of_cliqueFree_forall_degree_le [LocallyFinite G] {k : ℕ} (hk : 3 ≤ k)
    (hc : G.CliqueFree (k + 1)) (hbd : ∀ v, G.degree v ≤ k) : G.Colorable k := by
  apply nonempty_hom_of_forall_finite_subgraph_hom
  intro G' hf
  classical
  have h' := fun v ↦ G'.coe_degree v ▸ (Subgraph.degree_le ..).trans (hbd ..)
  haveI : Fintype ↑G'.verts := hf.fintype
  exact ((BrooksPart hk (hc.of_hom G'.hom) h' univ).some.copy coe_univ).toColoring

lemma two_colorable_iff_no_odd_cycle :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), w.IsCycle → ¬ Odd w.length := by
  rw [two_colorable_iff_forall_loop_not_odd]
  constructor <;> intro ho
  · intro _ w _ h
    exact ho _ _ h
  · classical
    intro _ w h
    exact ho _ _ (w.oddCycle_isCycle h) (w.oddCycle_is_odd h)

end SimpleGraph
