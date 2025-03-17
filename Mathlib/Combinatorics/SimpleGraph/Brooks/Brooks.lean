import Mathlib.Combinatorics.SimpleGraph.Brooks.PartialColoring

namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
open Finset


/-!
## Brooks' Theorem (a version of)
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
`C : G.PartialColoring s.erase v`then use `C.insert_extend a`
(the coloring of `s` given by greedyily extending `C`) to complete the proof.

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

open PartialColoring Walk
variable {k : ℕ} [Fintype α] [DecidableRel G.Adj] [DecidableEq α] {s : Finset α}


theorem BrooksPartial (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k)
    (s : Finset α) : ∃ C : G.PartialColoring s, ∀ v, C v < k := by
  have H  (n : ℕ) (hn : #s ≤ n) : ∃ C : G.PartialColoring s, ∀ v,  C v < k := by
    induction n using Nat.strong_induction_on generalizing s with
    | h n ih =>
    by_cases hd : ∃ v ∈ s, G.degreeOn (s.erase v) v < k
    · obtain ⟨v, hv, hlt⟩ := hd
      obtain ⟨C, hC⟩:= ih _ (Nat.lt_of_lt_of_le (card_erase_lt_of_mem hv) hn) _ le_rfl
      have hvlt : C.extend v < k := (C.extend_le_degreeOn _).trans_lt hlt
      have (w : α)  := insert_lt_of_lt hC hvlt w
      use (C.insert_extend v).copy (by simp_all)
      exact this
    push_neg at hd
    replace hd : ∀ v ∈ s, G.degreeOn (s.erase v) v = k := fun v hv ↦ le_antisymm
          ((degreeOn_le_degree ..).trans (hbdd v)) <| hd _ hv
    have hbdd' : ∀ v, v ∈ s → G.degree v = k := fun v hv ↦ le_antisymm (hbdd v)
          <| hd v hv ▸ degreeOn_le_degree ..
    have hins : ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s := by
      by_contra! hf
      obtain ⟨v, hv, w, ha, hns⟩ := hf
      have := degreeOn_lt_degree ⟨by rwa [← mem_neighborFinset] at ha, hns⟩
      rw [← degreeOn_erase, hd _ hv] at this
      exact this.not_le (hbdd v)
    by_cases hem : s.Nonempty
    · obtain ⟨v₂, hv₂⟩ := hem
      have nc := hc <| insert v₂ (G.neighborFinset v₂ ∩ s)
      have ⟨v₁, v₃, h1, h3, hne, hnadj⟩ : ∃ v₁ v₃, v₁ ∈ G.neighborFinset v₂ ∩ s ∧
          v₃ ∈ G.neighborFinset v₂ ∩ s ∧ v₁ ≠ v₃ ∧ ¬ G.Adj v₁ v₃ := by
        contrapose! nc
        apply IsNClique.insert
          ⟨fun _ ha _ hb hne ↦ nc _ _ ha hb hne, by rw [← hd _ hv₂, degreeOn_erase]⟩
        intro b hb; rw [mem_inter, mem_neighborFinset] at hb
        exact hb.1
      have ⟨v₄, h24, h4⟩ : ∃ v₄, G.Adj v₃ v₄ ∧ v₄ ≠ v₂ := by
        simp_rw [← mem_neighborFinset, Ne, ← mem_singleton, ← mem_sdiff]
        apply card_pos.1
        apply lt_of_lt_of_le _ (le_card_sdiff {v₂} (G.neighborFinset v₃))
        rw [card_neighborFinset_eq_degree, card_singleton, tsub_pos_iff_lt]
        exact (Nat.lt_of_succ_lt hk).trans_le (hbdd' v₃ (mem_inter.1 h3).2).symm.le
      rw [mem_inter, mem_neighborFinset] at h1 h3
      rw [adj_comm] at h3
      let v41 := ((Walk.cons h1.1 nil).cons h3.1).cons h24.symm
      have h41 : v41.IsPath := by
        rw [cons_isPath_iff]
        simp only [cons_isPath_iff, isPath_iff_eq_nil, support_nil, List.mem_cons,
         List.not_mem_nil, or_false, true_and, support_cons, not_or]
        exact ⟨⟨h1.1.ne, h3.1.ne, hne.symm⟩, h24.symm.ne, h4 ,fun hf ↦ hnadj (hf ▸ h24.symm)⟩
      have v41sup : v41.support = [v₄, v₃, v₂, v₁] := by
        rw [support_cons, support_cons, support_cons, support_nil]
      have v41s : ∀ y, y ∈ v41.support → y ∈ s := by
        intro x hx; rw [support_cons, support_cons, support_cons, support_nil] at hx
        cases hx with
        | head as => exact hins _ h3.2 _ h24
        | tail b hx =>
          cases hx with
          | head as => exact h3.2
          | tail b hx =>
            cases hx with
            | head as => exact hv₂
            | tail b hx =>
              cases hx with
              | head as => exact h1.2
              | tail b _ => contradiction
      obtain ⟨vᵣ, q, hq, hss, hmax⟩ : ∃ vᵣ, ∃ q : G.Walk vᵣ v₄, (q.append v41).IsPath ∧
        (∀ y, y ∈ (q.append v41).support → y ∈ s) ∧
          ∀ y, G.Adj vᵣ y → y ∈ ((q.append v41)).support := by

        obtain ⟨vᵣ, q, hq, hs, hnb⟩ := exists_maximal_path_subset s h41 v41s
        use vᵣ, q, hq, hs
        have vrs : vᵣ ∈ s := by apply hs; simp
        intro x hx
        have := (G.degreeOn_erase s vᵣ) ▸ ((hbdd vᵣ).trans (hd vᵣ vrs).symm.le)
        rw [← mem_neighborFinset] at hx
        rw [degree_le_degreeOn_iff] at this
        apply hnb
        apply mem_inter.2 ⟨hx, this hx⟩
      have hdisj2 := (append_isPath_iff.1 hq).2.2
      by_cases hr : ((q.append v41)).support.toFinset = s
      · --sorry
        --Main case 1

        rw [support_append, v41sup, List.tail,List.toFinset_append] at hr
        simp only [List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq] at hr
        rw [v41sup, List.tail] at hdisj2
        obtain ⟨vⱼ, hj⟩ : ∃ vⱼ, G.Adj v₂ vⱼ ∧ vⱼ ≠ v₁ ∧ vⱼ ≠ v₃ ∧ vⱼ ∈ s := by
          have := hk.trans <| (hd _ hv₂) ▸ (degreeOn_le_degree ..)
          rw [← card_neighborFinset_eq_degree] at this
          have :  1 ≤ #((G.neighborFinset v₂) \ {v₁, v₃}) := by
            rw [card_sdiff]
            · rw [card_pair hne]
              omega
            · intro x hx; simp only [mem_insert, mem_singleton, mem_neighborFinset] at *
              cases hx with
              | inl h => exact h ▸ h1.1
              | inr h => exact h ▸ h3.1.symm
          obtain ⟨vⱼ, hj⟩ := card_pos.1 this
          use vⱼ
          simp only [mem_sdiff, mem_neighborFinset, mem_insert, mem_singleton, not_or] at hj
          exact ⟨hj.1, hj.2.1, hj.2.2, hins _ hv₂ _ hj.1⟩
        have :  s = {v₁, v₂, v₃} ∪ q.support.toFinset := by
          rw [←hr, union_comm]
          congr! 1
          rw [insert_comm, insert_comm v₁]
          congr! 1
          exact pair_comm _ _
        convert Brooks1' q hk hj.1.symm hbdd hq.of_append_left (by aesop) h1.1 h3.1.symm hne
          hnadj (by aesop)  (by aesop)

      · -- Main case 2
        have hssf :(q.append v41).support.toFinset ⊂ s :=
          Finset.ssubset_iff_subset_ne.2 ⟨fun y hy ↦ hss _ <| List.mem_toFinset.1 hy, hr⟩
        have  h1 : 1 < G.degree vᵣ := Nat.lt_of_succ_lt <| hk.trans
          (hbdd' _ <| hss _ <| start_mem_support ..).symm.le
        set p := (q.append v41).reverse with hpq
        have hp : p.IsPath := hq.reverse
        have hcmp :=  IsCloseableMaxPath.mk' hp
          (by simp_rw [hpq, support_reverse, List.mem_reverse]; exact hmax) h1
        let c:= ((p.dropUntil p.close find_mem_support).cons hcmp.isClosable.adj)
        have hps : p.support = (q.append v41).support.reverse :=by rw [support_reverse]
        have ⟨hcy, hcym⟩ := IsMaxCycle.dropUntil_of_isClosableMaxPath <| IsCloseableMaxPath.mk' hp
          (by simp_rw [hpq, support_reverse, List.mem_reverse]; exact hmax) h1
        change c.IsCycle at hcy
        change c.IsMaximal at hcym
        rw [IsMaximal.iff] at hcym
        have hsub : c.support.toFinset ⊂ s := by
          apply Finset.ssubset_of_subset_of_ssubset _ hssf
          intro y hy
          rw [List.mem_toFinset] at *
          rw [support_cons] at hy
          cases hy with
          | head as => exact start_mem_support ..
          | tail b hy =>
            have := (support_dropUntil_subset _ _) hy
            rw [support_reverse] at this
            rwa [List.mem_reverse] at this
        have hnemp : 0 < #c.support.toFinset := by
          apply card_pos.2;
          use vᵣ
          rw [List.mem_toFinset]
          exact start_mem_support ..
        have hccard : #c.support.toFinset < n := (card_lt_card hsub).trans_le hn
        have hsdcard : #(s \ c.support.toFinset) < n := by
          rw [card_sdiff hsub.1]
          apply lt_of_lt_of_le _ hn
          rw [Nat.sub_lt_iff_lt_add (card_le_card hsub.1)]
          exact Nat.lt_add_of_pos_left hnemp
         -- Two cases either cycle has no neighbors outside of c
        by_cases hnbc : ∃ x, x ∈ c.support ∧ ∃ y, y ∈ s \ c.support.toFinset ∧ G.Adj x y
        · obtain ⟨x, hx, y, hy, had⟩ := hnbc
          let S : Set α := {a |  ∃ b ∈ s \ c.support.toFinset, G.Adj a b}
          have xS : x ∈ S := ⟨ _, hy, had⟩
          have rS : vᵣ ∉ S := fun ⟨ _, hy , had⟩ ↦
              (mem_sdiff.1 hy).2 <| List.mem_toFinset.2 <| hcym _ had
          obtain ⟨d, hd, ⟨y, hy1, hd1⟩, hd2⟩ :=
            exists_boundary_dart_of_closed c _ xS rS hx (start_mem_support ..)
          replace hd2 : ∀ b ∈ s \ c.support.toFinset, ¬ G.Adj d.toProd.2 b := by
            contrapose! hd2 ; exact hd2
          obtain ⟨C₁, hC₁⟩:= ih _ hsdcard _ le_rfl
          -- we know `hcym : vᵣ` has all its neighbors in `c` while
          -- `hnbc : ∃ x ∈ c` that has a neighbor in `s \ c`
          let C₂ := C₁.insertNotAdj hd2 y
          have hC₂ := C₁.lt_of_insertNotAdj_lt hd2 y hC₁
          let hr := (c.dart_fst_mem_support_of_mem_darts hd)
          let p := (c.rotate hr).tail.tail
          have hp : p.IsPath := (hcy.rotate hr).isPath_tail.tail
          have hne : d.toProd.2 ≠ y := by
            intro hf; subst_vars
            exact (mem_sdiff.1 hy1).2
            <| List.mem_toFinset.2 (c.dart_snd_mem_support_of_mem_darts hd)
          have hc2eq : C₂ d.toProd.2 = C₂ y := C₁.eq_ofinsertNotAdj hd2
          let C₃ := C₂.Greedy p.reverse.support
          have heq : (insert d.toProd.2 (s \ c.support.toFinset)
            ∪ p.reverse.support.toFinset) = s := by sorry
          use C₃.copy heq
          simp_rw [copy_eq]
          exact C₂.Greedy_of_path_notInj hbdd hp.reverse hC₂ (mem_insert_self _ _)
             (mem_insert_of_mem hy1)  d.adj hd1 hne hc2eq (by sorry)
        ·  -- Can now color `c` and `s \ c` by induction
          obtain ⟨C₁, hC₁⟩:= ih _ hccard  _ le_rfl
          obtain ⟨C₂, hC₂⟩:= ih _ hsdcard _ le_rfl
          push_neg at hnbc
          use (C₁.join C₂ (by simpa using hnbc)).copy (union_sdiff_of_subset hsub.1)
          intro v; rw [copy_eq]
          apply C₁.join_lt_of_lt hC₁ hC₂
    · rw [not_nonempty_iff_eq_empty] at hem
      use (ofEmpty G).copy hem.symm
      intros
      rw [copy_eq, ofEmpty_eq]
      exact Nat.zero_lt_of_lt hk
  exact H #s le_rfl



theorem Brooks (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k) :
    G.Colorable k := by
  rw [colorable_iff_exists_bdd_nat_coloring]
  obtain ⟨C, heq⟩ := BrooksPartial hk hc hbdd (univ : Finset α)
  exact ⟨⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩, by simpa using heq⟩

end SimpleGraph
