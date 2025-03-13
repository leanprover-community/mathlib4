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
/-- Essentially the first main case of Brooks theorem, applied with `s = {x₁, x₃}` -/
theorem Brooks1 {x₁ x₂ x₃ x₄ xⱼ xᵣ a : α} {p : G.Walk xᵣ x₄} (hk : 0 < k)
    {hc : G.Adj xⱼ x₂} (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support)
    (hs1 : x₁ ∈ s) (hs3 : x₃ ∈ s) (h21 : G.Adj x₂ x₁) (h23 : G.Adj x₂ x₃)
    (hne : x₁ ≠ x₃) (heq : ¬ G.Adj x₁ x₃) (hdisj : Disjoint s p.support.toFinset)
    (h2disjp : x₂ ∉ p.support) : ((G.ofNotAdj heq).Greedy (p.dropUntil _ hj).support.tail).Greedy
        ((p.takeUntil _ hj).concat hc).reverse.support a < k := by
  have hx1p : x₁ ∉ p.support := fun hf ↦ (disjoint_left.1 hdisj hs1 (List.mem_toFinset.2 hf))
  have hx3p : x₃ ∉ p.support := fun hf ↦ (disjoint_left.1 hdisj hs3 (List.mem_toFinset.2 hf))
  have htp := (concat_isPath_iff _ hc).2 ⟨hp.takeUntil hj,
      fun a ↦ h2disjp ((support_takeUntil_subset p hj) a)⟩
  let C₁ := (G.ofNotAdj heq).Greedy (p.dropUntil _ hj).support.tail
  have (x) : C₁ x < k := by
    have hd : ∀ y, y ∈ (p.dropUntil _ hj).support.toFinset → y ∈  p.support.toFinset := by
      intro y hy; rw [List.mem_toFinset] at *
      apply support_dropUntil_subset p hj hy
    have hd' : ∀ y : α, y ∈ ({x₁, x₃} : Finset α) → y ∈ s := by
      intro y hy; simp only [mem_insert, mem_singleton] at hy
      cases hy <;> subst_vars <;> assumption
    apply (G.ofNotAdj heq).Greedy_of_tail_path hbdd (hp.dropUntil hj)
      (fun y ↦ by rwa [ofNotAdj_eq heq])
    exact disjoint_of_subset_left hd' <| (disjoint_of_subset_right hd) hdisj
  let C₂ := C₁.Greedy ((p.takeUntil _ hj).concat hc).reverse.support
  have hc13 : C₁ x₁ = C₁ x₃ := by
    rw [Greedy_not_mem, Greedy_not_mem]
    · rfl
    · intro hf
      apply hx3p <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)
    · intro hf
      apply hx1p <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)
  apply C₁.Greedy_of_path_concat_notInj hbdd htp this _ _ h21 h23 hne hc13
  · simp_all only [ne_eq, concat_isPath_iff, insert_union, support_concat, List.concat_eq_append,
    List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
    disjoint_union_right, disjoint_insert_left, List.mem_toFinset, disjoint_union_left,
    disjoint_singleton_left, List.disjoint_toFinset_iff_disjoint, disjoint_singleton_right,
    mem_insert, mem_union, mem_singleton, not_or]
    refine ⟨⟨?_,?_,?_⟩,⟨?_,?_,?_⟩⟩
    · intro hf; apply hx1p <| (support_takeUntil_subset _ hj) hf
    · intro hf; apply hx3p <| (support_takeUntil_subset _ hj) hf
    · exact (hp.support_takeUntil_disjoint_dropUntil_tail hj).symm
    · exact h21.ne
    · exact h23.ne
    · intro hf; apply h2disjp <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)
  · apply mem_union_left  _ (by simp)
  · apply mem_union_left  _ (by simp)




set_option maxHeartbeats 2000000

theorem BrooksPartial (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k)
    (s : Finset α) : ∃ C : G.PartialColoring s, ∀ v, v ∈ s → C v < k := by
  have H  (n : ℕ) (hn : #s ≤ n) : ∃ C : G.PartialColoring s, ∀ v, v ∈ s → C v < k := by
    induction n using Nat.strong_induction_on generalizing s with
    | h n ih =>
    by_cases hd : ∃ v ∈ s, G.degreeOn (s.erase v) v < k
    · obtain ⟨v, hv, hlt⟩ := hd
      obtain ⟨C, hC⟩:= ih _ (Nat.lt_of_lt_of_le (card_erase_lt_of_mem hv) hn) _ le_rfl
      have hvlt : C.extend v < k := (C.extend_le_degreeOn _).trans_lt hlt
      have (w : α) (hw : w ∈ insert v (s.erase v)) := insert_lt_of_lt hC hvlt hw
      use (C.insert_extend v).copy (by simp_all)
      convert this
      rw [insert_erase hv]
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
        simp only [cons_isPath_iff, isPath_iff_eq_nil, support_nil, List.mem_cons, List.not_mem_nil,
          or_false, true_and, support_cons, not_or]
        exact ⟨⟨h1.1.ne, h3.1.ne, hne.symm⟩, h24.symm.ne, h4 ,fun hf ↦ hnadj (hf ▸ h24.symm)⟩
      have v41sup : v41.support = [v₄, v₃, v₂, v₁] := by
        rw [support_cons, support_cons, support_cons, support_nil]
      have v41s : ∀ y, y ∈  v41.support → y ∈ s := by
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
      · -- Main case 1
        -- TODO work out what the last ∧ condition should be below
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
        let C₁ := G.ofNotAdj hnadj
        have ms : ∀ v, v ∈ s → v ≠ v₁ → v ≠ v₂ → v ≠ v₃ → v ∈ q.support := by
          intro v hv hv1 hv2 hv3
          have := hr.symm.le hv
          rw [support_append, support_cons, support_cons, support_cons, support_nil, List.tail,
            List.mem_toFinset] at this
          rw [List.mem_append] at this
          cases this with
          | inl h => exact h
          | inr h => simp_all only [ne_eq, mem_support_append_iff, List.mem_cons, List.not_mem_nil,
            or_self]
        have vjm :=(ms vⱼ hj.2.2.2 hj.2.1 hj.1.symm.ne hj.2.2.1)
        have h4r : vᵣ ≠ v₄ := by sorry
        by_cases h4j : vⱼ = v₄
        · subst vⱼ
          --obtain ⟨v₅, q', h₅₄, heq⟩ := q.exists_eq_concat_of_ne h4r
          let C₂ := C₁.Greedy q.reverse.support
          have h2r : (q.concat hj.1.symm).IsPath := by
            apply hq.of_append_left.concat
            intro h2
            rw [isPath_def, support_append, List.nodup_append] at hq
            apply hq.2.2 h2 (by rw [support_cons, support_cons, support_cons, List.tail]; simp)
          have hc2 x : C₂ x < k := by

            apply C₁.Greedy_of_concat_path hbdd h2r
               (fun y ↦ (ofNotAdj_eq hnadj _) ▸ (Nat.zero_lt_of_lt hk))
            rw [append_isPath_iff, v41sup, List.tail] at hq
            aesop
          have heq : ({v₁, v₃} ∪ q.reverse.support.toFinset) ∪ [v₂].toFinset = s := by
            rw [← hr, support_append, v41sup, List.tail, support_reverse]
            aesop
          use (C₂.Greedy [v₂]).copy heq
          have : C₂.extend v₂ < k := by
            apply (extend_lt_of_not_injOn _ _  h1.1 h3.1.symm hne _).trans_le <|
              (degreeOn_le_degree ..).trans (hbdd v₂)
            · simp
            · simp
            · rw [v41sup, List.tail] at hdisj2
              rw [Greedy_not_mem, Greedy_not_mem]
              · rfl
              · intro hf; rw [support_reverse,List.mem_reverse] at hf; apply hdisj2 hf
                simp
              · intro hf; rw [support_reverse,List.mem_reverse] at hf; apply hdisj2 hf
                simp
          simp_rw [copy_eq]
          intro x hx
          by_cases hxv₂ : x = v₂
          · rw [hxv₂, C₂.Greedy_head, C₂.Greedy_nil]
            rwa [copy_extend]
          · rw [Greedy_not_mem (by simpa using hxv₂)]
            exact hc2 _
        ·          -- NEXT decide whether concat/cons is correct
          let q₁ := q.takeUntil vⱼ vjm
          let q₂ := q.dropUntil vⱼ vjm
          obtain ⟨vⱼ', q₂',h1, heq⟩ := q₂.exists_eq_concat_of_ne h4j

          have hqp :=hq.of_append_left
          have hqp : q₁.IsPath ∧ q₂.IsPath := by
            rw [← take_spec _ vjm] at hqp
            exact ⟨hqp.of_append_left, hqp.of_append_right⟩
          let C₂ := C₁.Greedy q₂'.reverse.support
          have (x) : C₂ x < k := C₁.Greedy_of_concat_path hbdd (heq ▸ hqp.2)
            (fun y ↦ (ofNotAdj_eq hnadj _) ▸ (Nat.zero_lt_of_lt hk)) (by sorry)
          sorry
      · -- Main case 2
        --replace hss := Finset.ssubset_iff_subset_ne.2 ⟨hss, hr⟩

        sorry

    · rw [not_nonempty_iff_eq_empty] at hem
      use (ofEmpty G).copy hem.symm
      intros
      rw [copy_eq, ofEmpty_eq]
      exact Nat.zero_lt_of_lt hk
  exact H #s le_rfl
#check Finset.two_lt_card



theorem Brooks (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k) :
    G.Colorable k := by
  rw [colorable_iff_exists_bdd_nat_coloring]
  obtain ⟨C, heq⟩ := BrooksPartial hk hc hbdd (univ : Finset α)
  exact ⟨⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩, by simpa using heq⟩

end SimpleGraph
