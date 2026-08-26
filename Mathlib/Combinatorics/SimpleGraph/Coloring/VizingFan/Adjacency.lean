/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VizingFan.Rotation

/-!
# Vizing Adjacency Lemma

This file proves the Vizing adjacency lemma from the fan and Kempe-chain
machinery.
-/

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

/-! ### Maximal Fans -/

set_option linter.unusedDecidableInType false in
/-- Every fan can be extended to a maximal fan (induction on `Fintype.card V − l.length`). -/
private lemma IsFan.exists_maximal
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} {c : G.lineGraph.Coloring α} :
    ∀ (gap : ℕ) (l : List V) (_h_ne : l ≠ []),
      IsFan c u v l → Fintype.card V - l.length ≤ gap →
      ∃ (l' : List V) (h_ne' : l' ≠ []),
        IsFan c u v l' ∧
        ∀ w : V, w ∉ l' → ¬ IsFanExtension c u (l'.getLast h_ne') w := by
  intro gap
  induction gap with
  | zero =>
    intro l h_ne h_fan h_gap
    have h_len_le : l.length ≤ Fintype.card V := h_fan.length_le_card
    have h_len_eq : l.length = Fintype.card V := by omega
    refine ⟨l, h_ne, h_fan, ?_⟩
    intro w hw_notin h_ext
    obtain ⟨_, h_nodup, _⟩ := h_fan
    have h_l'_nodup : (l ++ [w]).Nodup := by
      apply List.Nodup.append h_nodup (List.nodup_singleton w)
      intro x hx_l hx_w
      rw [List.mem_singleton] at hx_w
      subst hx_w
      exact hw_notin hx_l
    have h_l'_len : (l ++ [w]).length = Fintype.card V + 1 := by
      simp [List.length_append, h_len_eq]
    have h_card_le : (l ++ [w]).length ≤ Fintype.card V := by
      classical
      rw [← List.toFinset_card_of_nodup h_l'_nodup]
      exact Finset.card_le_univ _
    omega
  | succ k ih =>
    intro l h_ne h_fan h_gap
    by_cases h_ext : ∃ w : V, w ∉ l ∧ IsFanExtension c u (l.getLast h_ne) w
    · obtain ⟨w, hw_notin, hw_ext⟩ := h_ext
      obtain ⟨h_head, h_nodup, h_chain⟩ := h_fan
      -- Extend l by w to get a longer fan.
      have h_l'_ne : (l ++ [w]) ≠ [] := by simp
      have h_l'_fan : IsFan c u v (l ++ [w]) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [List.head?_append_of_ne_nil _ h_ne]
          exact h_head
        · apply List.Nodup.append h_nodup (List.nodup_singleton w)
          intro x hx_l hx_w
          rw [List.mem_singleton] at hx_w
          subst hx_w
          exact hw_notin hx_l
        · apply List.IsChain.append h_chain (List.isChain_singleton w)
          intro x hx_last y hy_head
          have hx : x = l.getLast h_ne := by
            have h := List.getLast?_eq_some_getLast h_ne
            rw [h] at hx_last
            exact (Option.mem_some_iff.mp hx_last).symm
          have hy : y = w := by
            have h : ([w] : List V).head? = some w := rfl
            rw [h] at hy_head
            exact (Option.mem_some_iff.mp hy_head).symm
          subst hx
          subst hy
          exact hw_ext
      have h_l'_gap : Fintype.card V - (l ++ [w]).length ≤ k := by
        simp [List.length_append]
        omega
      exact ih (l ++ [w]) h_l'_ne h_l'_fan h_l'_gap
    · push Not at h_ext
      exact ⟨l, h_ne, h_fan, h_ext⟩

/-! ### Vizing's Adjacency Lemma -/

/-- Core case analysis for `vizingAdjacencyLemma`. Accepts a pre-built maximal
    fan `l` and its maximality witness `h_max`, then dispatches on Term-A /
    Term-B. In the Term-B case, a Kempe chain swap is performed to create a
    shared free color, reducing to Term-A. -/
private lemma vizingAdjacencyLemma_aux
    [Fintype V] [Fintype α] [DecidableRel G.Adj]
    {u v : V} (e_uv : G.edgeSet) (he_uv : e_uv.val = s(u, v))
    (h_card : G.maxDegree < Fintype.card α)
    (c : (G.deleteEdges {e_uv.val}).lineGraph.Coloring α)
    (l : List V)
    (h_ne : l ≠ [])
    (h_fan : IsFan c u v l)
    (h_max : ∀ w : V, w ∉ l → ¬ IsFanExtension c u (l.getLast h_ne) w)
    (h_missing_u : (missingColors c u).Nonempty)
    (_h_missing_v : (missingColors c v).Nonempty)
    (_h_missing_u_card : 2 ≤ (missingColors c u).ncard) :
    Nonempty (G.lineGraph.Coloring α) := by
  classical
  by_cases h_common : ∃ γ : α, γ ∈ missingColors c u ∧ γ ∈ missingColors c v
  · -- Case A: a common missing color exists — extend directly.
    obtain ⟨γ, hγ_u, hγ_v⟩ := h_common
    exact extendColoring_of_missingColors_both e_uv he_uv c γ hγ_u hγ_v
  · -- Case B: no common missing color. Use the fan + Kempe argument.
    push Not at h_common
    rcases IsFan.dichotomy h_fan h_ne h_max with h_term_a | h_term_b
    · -- Term-A: a color γ is missing at both u and vₖ.
      obtain ⟨γ, hγ_u, hγ_vk⟩ := h_term_a
      exact IsFan.rotateTermA e_uv he_uv h_fan h_ne γ hγ_u hγ_vk
    · -- Term-B: every colour missing at vₖ is realised by a fan edge.
      set v_k := l.getLast h_ne with hv_k_def
      obtain ⟨a, ha_u⟩ := h_missing_u
      have h_missing_vk : (missingColors c v_k).Nonempty := by
        apply missingColors_nonempty_of_degree_lt c v_k
        have h_deg_le : (G.deleteEdges {e_uv.val}).degree v_k ≤ G.degree v_k :=
          SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)
        have h_deg_max : G.degree v_k ≤ G.maxDegree := G.degree_le_maxDegree v_k
        omega
      obtain ⟨b, hb_vk⟩ := h_missing_vk
      obtain ⟨v_j, hv_j_mem, e_b, he_b_val, he_b_col⟩ := h_term_b b hb_vk
      have hb_inc_u : b ∈ incidentColors c u := by
        refine ⟨e_b, ?_, he_b_col⟩
        change u ∈ e_b.val
        rw [he_b_val]; exact Sym2.mem_mk_left u v_j
      have h_a_ne_b : a ≠ b := by
        intro h_eq
        apply ha_u
        rw [h_eq]; exact hb_inc_u
      by_cases h_reach : (kempeSubgraph c a b).Reachable u v_k
      · -- Sub-case B2: `u` and `vₖ` in the same αβ-component.
        have h_eb_inSZ : inSwapZone c a b u e_b := by
          refine ⟨Or.inr he_b_col, u, ?_, SimpleGraph.Reachable.refl u⟩
          rw [he_b_val]; exact Sym2.mem_mk_left u v_j
        have h_b_missing_u : b ∈ missingColors (swapKempe c a b u) u := by
          intro h_inc
          obtain ⟨e', he'_inc, he'_col⟩ := h_inc
          by_cases h_swap : inSwapZone c a b u e'
          · rw [swapKempe_toFun_of_inSwapZone c a b u h_swap] at he'_col
            have h_c_e' : c.toFun e' = a := by
              apply swapColors_injective a b
              rw [he'_col, swapColors_a]
            exact ha_u ⟨e', he'_inc, h_c_e'⟩
          · rw [swapKempe_toFun_of_not_inSwapZone c a b u h_swap] at he'_col
            have h_e'_ne_eb : e' ≠ e_b := by
              intro h_eq; subst h_eq; exact h_swap h_eb_inSZ
            have h_e_b_at_u : u ∈ e_b.val := by
              rw [he_b_val]; exact Sym2.mem_mk_left u v_j
            have h_lg_adj : (G.deleteEdges {e_uv.val}).lineGraph.Adj e' e_b :=
              ⟨h_e'_ne_eb, u, he'_inc, h_e_b_at_u⟩
            exact c.valid h_lg_adj (he'_col.trans he_b_col.symm)
        have h_u_ne_vj : u ≠ v_j := by
          have h_adj : (G.deleteEdges {e_uv.val}).Adj u v_j := by
            have hp := e_b.property
            rw [he_b_val] at hp
            exact (SimpleGraph.mem_edgeSet _).mp hp
          exact h_adj.ne
        have h_vj_ne_v : v_j ≠ v := by
          intro h_eq
          have h_val_eq : e_b.val = e_uv.val := by
            rw [he_b_val, h_eq]; exact he_uv.symm
          have h_in_diff : e_b.val ∈ G.edgeSet \ {e_uv.val} := by
            rw [← SimpleGraph.edgeSet_deleteEdges]
            exact e_b.property
          exact h_in_diff.2 h_val_eq
        obtain ⟨l_pre, l_post, hl_split⟩ : ∃ s t, l = s ++ v_j :: t :=
          List.append_of_mem hv_j_mem
        have h_l_pre_ne : l_pre ≠ [] := by
          intro h_pre_nil
          rw [h_pre_nil, List.nil_append] at hl_split
          obtain ⟨h_head, _, _⟩ := h_fan
          rw [hl_split] at h_head
          simp only [List.head?_cons, Option.some.injEq] at h_head
          exact h_vj_ne_v h_head
        set v_jm1 := l_pre.getLast h_l_pre_ne with hv_jm1_def
        have h_vj_not_in_lpre : v_j ∉ l_pre := by
          obtain ⟨_, h_nodup_l, _⟩ := h_fan
          rw [hl_split, List.nodup_append'] at h_nodup_l
          intro h_in
          exact h_nodup_l.2.2 h_in List.mem_cons_self
        have hb_missing_vjm1 : b ∈ missingColors c v_jm1 := by
          obtain ⟨_, _, h_chain⟩ := h_fan
          rw [hl_split] at h_chain
          obtain ⟨_, _, h_boundary⟩ := List.isChain_append.mp h_chain
          have h_pre_last : v_jm1 ∈ l_pre.getLast? := by
            rw [List.getLast?_eq_some_getLast h_l_pre_ne]; rfl
          have h_post_head : v_j ∈ (v_j :: l_post).head? := rfl
          obtain ⟨e, he_val, he_col⟩ := h_boundary v_jm1 h_pre_last v_j h_post_head
          have h_e_eq_eb : e = e_b := by
            apply Subtype.ext
            rw [he_val, he_b_val]
          rw [h_e_eq_eb, he_b_col] at he_col
          exact he_col
        -- Three-endpoint lemma: u, vₖ, v_{j-1} all have degree ≤ 1 in the
        -- Kempe subgraph but lie in the same component — contradiction.
        have h_not_reach_jm1 :
            ¬ (kempeSubgraph c a b).Reachable u v_jm1 := by
          intro h_rj
          classical
          set H := kempeSubgraph c a b with hH_def
          set C := H.connectedComponentMk u with hC_def
          have hu_C : u ∈ C.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
          have hvk_C : v_k ∈ C.supp := by
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
            exact (SimpleGraph.ConnectedComponent.eq).mpr h_reach.symm
          have hvjm1_C : v_jm1 ∈ C.supp := by
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
            exact (SimpleGraph.ConnectedComponent.eq).mpr h_rj.symm
          have h_u_ne_v : u ≠ v := by
            have h_adj : G.Adj u v := G.mem_edgeSet.mp (he_uv ▸ e_uv.property)
            exact h_adj.ne
          have h_u_not_in_l : u ∉ l := by
            obtain ⟨h_head, _, h_chain⟩ := h_fan
            intro h_u_mem
            obtain ⟨i, hi_lt, h_get⟩ := List.getElem_of_mem h_u_mem
            rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
            · subst hi0
              have h_head_get : l[0] = v := by
                have : l.head? = some v := h_head
                rw [List.head?_eq_getElem?] at this
                simp only [List.getElem?_eq_getElem hi_lt, Option.some.injEq] at this
                exact this
              rw [h_head_get] at h_get
              exact h_u_ne_v h_get.symm
            · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
              have h_chain' : List.IsChain _ l := h_chain
              have h_rel := h_chain'.getElem j hi_lt
              obtain ⟨e, he_val, _⟩ := h_rel
              rw [h_get] at he_val
              have h_adj : (G.deleteEdges {e_uv.val}).Adj u u :=
                (SimpleGraph.mem_edgeSet _).mp (he_val ▸ e.property)
              exact (G.deleteEdges {e_uv.val}).irrefl h_adj
          have h_vk_in_l : v_k ∈ l := by
            rw [hv_k_def]
            exact List.getLast_mem h_ne
          have h_vjm1_in_l : v_jm1 ∈ l := by
            have h_vjm1_in_lpre : v_jm1 ∈ l_pre := by
              rw [hv_jm1_def]
              exact List.getLast_mem h_l_pre_ne
            rw [hl_split]
            exact List.mem_append_left _ h_vjm1_in_lpre
          have h_u_ne_vk : u ≠ v_k := fun h_eq => h_u_not_in_l (h_eq ▸ h_vk_in_l)
          have h_u_ne_vjm1 : u ≠ v_jm1 := fun h_eq => h_u_not_in_l (h_eq ▸ h_vjm1_in_l)
          have h_vk_ne_vjm1 : v_k ≠ v_jm1 := by
            intro h_eq
            obtain ⟨_, h_nodup_l, _⟩ := h_fan
            have h_vjm1_in_lpre : v_jm1 ∈ l_pre := by
              rw [hv_jm1_def]; exact List.getLast_mem h_l_pre_ne
            have h_l_post_ne : (v_j :: l_post) ≠ [] := List.cons_ne_nil v_j l_post
            have h_vk_eq : v_k = (v_j :: l_post).getLast h_l_post_ne := by
              rw [hv_k_def]
              have : l = l_pre ++ (v_j :: l_post) := hl_split
              clear_value v_k
              subst this
              exact List.getLast_append_of_right_ne_nil l_pre _ h_l_post_ne
            have h_vk_in_post : v_k ∈ v_j :: l_post := by
              rw [h_vk_eq]
              exact List.getLast_mem h_l_post_ne
            rw [hl_split, List.nodup_append'] at h_nodup_l
            exact h_nodup_l.2.2 (h_eq ▸ h_vjm1_in_lpre) h_vk_in_post
          have h_deg_u :
              (H.neighborSet u).ncard ≤ 1 :=
            kempeSubgraph_neighborSet_ncard_le_one_of_missing_left c a b u ha_u
          have h_deg_vk :
              (H.neighborSet v_k).ncard ≤ 1 :=
            kempeSubgraph_neighborSet_ncard_le_one_of_missing_right c a b v_k hb_vk
          have h_deg_vjm1 :
              (H.neighborSet v_jm1).ncard ≤ 1 :=
            kempeSubgraph_neighborSet_ncard_le_one_of_missing_right c a b v_jm1
              hb_missing_vjm1
          set K := C.toSimpleGraph with hK_def
          have hK_conn : K.Connected := C.connected_toSimpleGraph
          let uC : (C.supp : Set V) := ⟨u, hu_C⟩
          let vkC : (C.supp : Set V) := ⟨v_k, hvk_C⟩
          let vjm1C : (C.supp : Set V) := ⟨v_jm1, hvjm1_C⟩
          have h_uC_ne_vkC : uC ≠ vkC := by
            intro h; apply h_u_ne_vk
            exact Subtype.mk.injEq .. |>.mp h
          have h_uC_ne_vjm1C : uC ≠ vjm1C := by
            intro h; apply h_u_ne_vjm1
            exact Subtype.mk.injEq .. |>.mp h
          have h_vkC_ne_vjm1C : vkC ≠ vjm1C := by
            intro h; apply h_vk_ne_vjm1
            exact Subtype.mk.injEq .. |>.mp h
          have hC_fintype : Fintype ↑C.supp := Fintype.ofFinite _
          have h_K_deg_le : ∀ (w : ↑C.supp) (m : ℕ),
              (H.neighborSet w.val).ncard ≤ m → K.degree w ≤ m := by
            intro w m hm
            have h_img_sub :
                Subtype.val '' (K.neighborSet w) ⊆ H.neighborSet w.val := by
              rintro y ⟨⟨y', hy'_C⟩, hy_adj, rfl⟩
              exact (C.toSimpleGraph_adj w.2 hy'_C).mp hy_adj
            have h_inj : Function.Injective
                (Subtype.val : ↑C.supp → V) := Subtype.val_injective
            have h_card_img : (Subtype.val '' (K.neighborSet w)).ncard =
                (K.neighborSet w).ncard :=
              Set.ncard_image_of_injective _ h_inj
            have h_ns_fin : (H.neighborSet w.val).Finite :=
              Set.toFinite _
            have h_ncard_le : (K.neighborSet w).ncard ≤
                (H.neighborSet w.val).ncard := by
              rw [← h_card_img]
              exact Set.ncard_le_ncard h_img_sub h_ns_fin
            have h_card_eq : Fintype.card (K.neighborSet w) =
                (K.neighborSet w).ncard := by
              rw [Set.ncard_eq_toFinset_card']
              exact (Set.toFinset_card _).symm
            have h_deg_eq : K.degree w =
                (K.neighborSet w).ncard := by
              rw [← SimpleGraph.card_neighborSet_eq_degree, h_card_eq]
            rw [h_deg_eq]
            exact h_ncard_le.trans hm
          have h_K_deg_u : K.degree uC ≤ 1 := h_K_deg_le uC 1 h_deg_u
          have h_K_deg_vk : K.degree vkC ≤ 1 := h_K_deg_le vkC 1 h_deg_vk
          have h_K_deg_vjm1 : K.degree vjm1C ≤ 1 := h_K_deg_le vjm1C 1 h_deg_vjm1
          have h_K_deg_le_two : ∀ w : ↑C.supp, K.degree w ≤ 2 := by
            intro w
            exact h_K_deg_le w 2
              (kempeSubgraph_neighborSet_ncard_le_two c a b w.val)
          have h_card_ge_three : 3 ≤ Fintype.card ↑C.supp := by
            have h_sub : ({uC, vkC, vjm1C} : Finset ↑C.supp) ⊆ Finset.univ := by
              intro x _; exact Finset.mem_univ x
            have h_card_set : ({uC, vkC, vjm1C} : Finset ↑C.supp).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                  Finset.card_singleton]
              · rw [Finset.mem_singleton]
                exact h_vkC_ne_vjm1C
              · rw [Finset.mem_insert, Finset.mem_singleton]
                push Not
                exact ⟨h_uC_ne_vkC, h_uC_ne_vjm1C⟩
            have h_le : ({uC, vkC, vjm1C} : Finset ↑C.supp).card ≤
                (Finset.univ : Finset ↑C.supp).card :=
              Finset.card_le_card h_sub
            rw [h_card_set, Finset.card_univ] at h_le
            exact h_le
          have h_sum_deg_le :
              ∑ w : ↑C.supp, K.degree w ≤ 2 * Fintype.card ↑C.supp - 3 := by
            classical
            have h_triple : ({uC, vkC, vjm1C} : Finset ↑C.supp).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                  Finset.card_singleton]
              · rw [Finset.mem_singleton]; exact h_vkC_ne_vjm1C
              · rw [Finset.mem_insert, Finset.mem_singleton]
                push Not; exact ⟨h_uC_ne_vkC, h_uC_ne_vjm1C⟩
            have h_triple_sub : ({uC, vkC, vjm1C} : Finset ↑C.supp) ⊆ Finset.univ :=
              fun x _ => Finset.mem_univ x
            have h_sum_split :
                ∑ w : ↑C.supp, K.degree w =
                  ∑ w ∈ ({uC, vkC, vjm1C} : Finset ↑C.supp), K.degree w +
                  ∑ w ∈ (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)),
                    K.degree w := by
              rw [← Finset.sum_union (Finset.disjoint_sdiff)]
              congr 1
              rw [Finset.union_sdiff_of_subset h_triple_sub]
            have h_triple_sum :
                ∑ w ∈ ({uC, vkC, vjm1C} : Finset ↑C.supp), K.degree w ≤ 3 := by
              rw [show ({uC, vkC, vjm1C} : Finset ↑C.supp) =
                  insert uC (insert vkC {vjm1C}) from rfl]
              rw [Finset.sum_insert (by
                rw [Finset.mem_insert, Finset.mem_singleton]
                push Not; exact ⟨h_uC_ne_vkC, h_uC_ne_vjm1C⟩),
                  Finset.sum_insert (by
                    rw [Finset.mem_singleton]; exact h_vkC_ne_vjm1C),
                  Finset.sum_singleton]
              calc K.degree uC + (K.degree vkC + K.degree vjm1C)
                  ≤ 1 + (1 + 1) := by
                    exact add_le_add h_K_deg_u (add_le_add h_K_deg_vk h_K_deg_vjm1)
                _ = 3 := by rfl
            have h_compl_card :
                (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)).card =
                  Fintype.card ↑C.supp - 3 := by
              rw [Finset.card_sdiff_of_subset h_triple_sub, h_triple,
                  Finset.card_univ]
            have h_compl_sum :
                ∑ w ∈ (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)),
                  K.degree w ≤ 2 * (Fintype.card ↑C.supp - 3) := by
              calc ∑ w ∈ (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)),
                    K.degree w
                  ≤ ∑ _ ∈ (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)),
                    2 := Finset.sum_le_sum (fun w _ => h_K_deg_le_two w)
                _ = 2 * (Finset.univ \ ({uC, vkC, vjm1C} : Finset ↑C.supp)).card := by
                    rw [Finset.sum_const, smul_eq_mul, mul_comm]
                _ = 2 * (Fintype.card ↑C.supp - 3) := by rw [h_compl_card]
            rw [h_sum_split]
            have h_expand :
                2 * Fintype.card ↑C.supp - 3 =
                  3 + 2 * (Fintype.card ↑C.supp - 3) := by omega
            rw [h_expand]
            exact add_le_add h_triple_sum h_compl_sum
          -- Lower bound: 2 * (card - 1) ≤ sum deg, via the tree bound.
          have h_sum_deg_eq :
              ∑ w : ↑C.supp, K.degree w = 2 * K.edgeFinset.card :=
            K.sum_degrees_eq_twice_card_edges
          have h_tree_bound :
              Nat.card ↑C.supp ≤ Nat.card K.edgeSet + 1 :=
            hK_conn.card_vert_le_card_edgeSet_add_one
          have h_nat_card_supp :
              Nat.card ↑C.supp = Fintype.card ↑C.supp :=
            Nat.card_eq_fintype_card
          have h_nat_card_edges :
              Nat.card K.edgeSet = K.edgeFinset.card := by
            rw [Nat.card_eq_fintype_card, ← K.edgeFinset_card]
          have h_tree_bound' :
              Fintype.card ↑C.supp ≤ K.edgeFinset.card + 1 := by
            rw [← h_nat_card_supp, ← h_nat_card_edges]
            exact h_tree_bound
          have h_sum_lower :
              2 * Fintype.card ↑C.supp - 2 ≤
                ∑ w : ↑C.supp, K.degree w := by
            rw [h_sum_deg_eq]
            omega
          omega
        -- Shortened fan in `c'` with `b` missing at both `u` and `v_{j-1}`.
        have h_l_pre_fan_c' : IsFan (swapKempe c a b u) u v l_pre := by
          obtain ⟨h_head_l, h_nodup_l, h_chain_l⟩ := h_fan
          refine ⟨?_, ?_, ?_⟩
          · rw [hl_split] at h_head_l
            rwa [List.head?_append_of_ne_nil _ h_l_pre_ne] at h_head_l
          · rw [hl_split] at h_nodup_l
            exact (List.nodup_append'.mp h_nodup_l).1
          · rw [hl_split] at h_chain_l
            have h_chain_pre := (List.isChain_append.mp h_chain_l).1
            apply h_chain_pre.imp_of_mem_imp
            intro a' b' _ha'_mem hb'_mem h_R_in_c
            obtain ⟨e, he_val, he_col⟩ := h_R_in_c
            refine ⟨e, he_val, ?_⟩
            have h_c_e_ne_a : c.toFun e ≠ a := by
              intro h_col_a
              apply ha_u
              refine ⟨e, ?_, h_col_a⟩
              change u ∈ e.val
              rw [he_val]; exact Sym2.mem_mk_left u b'
            have h_b'_ne_vj : b' ≠ v_j := fun h => h_vj_not_in_lpre (h ▸ hb'_mem)
            have h_c_e_ne_b : c.toFun e ≠ b := by
              intro h_col_b
              have h_u_in_e : u ∈ e.val := by
                rw [he_val]; exact Sym2.mem_mk_left u b'
              have h_u_in_eb : u ∈ e_b.val := by
                rw [he_b_val]; exact Sym2.mem_mk_left u v_j
              have h_e_eq_eb : e = e_b := by
                by_contra h_ne_eb
                have h_lg_adj : (G.deleteEdges {e_uv.val}).lineGraph.Adj e e_b :=
                  ⟨h_ne_eb, u, h_u_in_e, h_u_in_eb⟩
                exact c.valid h_lg_adj (h_col_b.trans he_b_col.symm)
              have h_val_eq : e.val = e_b.val := h_e_eq_eb ▸ rfl
              rw [he_val, he_b_val, Sym2.eq_iff] at h_val_eq
              rcases h_val_eq with ⟨_, h_b'_eq_vj⟩ | ⟨h_u_eq_vj, _⟩
              · exact h_b'_ne_vj h_b'_eq_vj
              · exact h_u_ne_vj h_u_eq_vj
            have h_e_not_swap : ¬ inSwapZone c a b u e := by
              rintro ⟨h_col_swap, _⟩
              rcases h_col_swap with h | h
              · exact h_c_e_ne_a h
              · exact h_c_e_ne_b h
            rw [swapKempe_toFun_of_not_inSwapZone c a b u h_e_not_swap]
            exact (mem_missingColors_swapKempe_iff_of_ne c u a' h_c_e_ne_a h_c_e_ne_b).mpr he_col
        have h_b_missing_vjm1_c' : b ∈ missingColors (swapKempe c a b u) v_jm1 := by
          rw [missingColors_swapKempe_of_not_reachable c a b u h_not_reach_jm1]
          exact hb_missing_vjm1
        exact IsFan.rotateTermA e_uv he_uv h_l_pre_fan_c' h_l_pre_ne b
          h_b_missing_u h_b_missing_vjm1_c'
      · -- Sub-case B1: `u` and `vₖ` in different αβ-components.
        have h_eb_inSZ : inSwapZone c a b u e_b := by
          refine ⟨Or.inr he_b_col, u, ?_, SimpleGraph.Reachable.refl u⟩
          rw [he_b_val]; exact Sym2.mem_mk_left u v_j
        have h_b_missing_u : b ∈ missingColors (swapKempe c a b u) u := by
          intro h_inc
          obtain ⟨e', he'_inc, he'_col⟩ := h_inc
          by_cases h_swap : inSwapZone c a b u e'
          · rw [swapKempe_toFun_of_inSwapZone c a b u h_swap] at he'_col
            have h_c_e' : c.toFun e' = a := by
              apply swapColors_injective a b
              rw [he'_col, swapColors_a]
            exact ha_u ⟨e', he'_inc, h_c_e'⟩
          · rw [swapKempe_toFun_of_not_inSwapZone c a b u h_swap] at he'_col
            have h_e'_ne_eb : e' ≠ e_b := by
              intro h_eq; subst h_eq; exact h_swap h_eb_inSZ
            have h_e_b_at_u : u ∈ e_b.val := by
              rw [he_b_val]; exact Sym2.mem_mk_left u v_j
            have h_lg_adj : (G.deleteEdges {e_uv.val}).lineGraph.Adj e' e_b :=
              ⟨h_e'_ne_eb, u, he'_inc, h_e_b_at_u⟩
            exact c.valid h_lg_adj (he'_col.trans he_b_col.symm)
        have h_b_missing_vk : b ∈ missingColors (swapKempe c a b u) v_k := by
          intro h_inc
          obtain ⟨e', he'_inc, he'_col⟩ := h_inc
          have h_e'_not_swap : ¬ inSwapZone c a b u e' := by
            intro h_swap
            exact h_reach (h_swap.both_endpoints_reachable he'_inc)
          rw [swapKempe_toFun_of_not_inSwapZone c a b u h_e'_not_swap] at he'_col
          exact hb_vk ⟨e', he'_inc, he'_col⟩
        have h_u_ne_vj : u ≠ v_j := by
          have h_adj : (G.deleteEdges {e_uv.val}).Adj u v_j := by
            have hp := e_b.property
            rw [he_b_val] at hp
            exact (SimpleGraph.mem_edgeSet _).mp hp
          exact h_adj.ne
        have h_vj_ne_v : v_j ≠ v := by
          intro h_eq
          have h_val_eq : e_b.val = e_uv.val := by
            rw [he_b_val, h_eq]; exact he_uv.symm
          have h_in_diff : e_b.val ∈ G.edgeSet \ {e_uv.val} := by
            rw [← SimpleGraph.edgeSet_deleteEdges]
            exact e_b.property
          exact h_in_diff.2 h_val_eq
        obtain ⟨l_pre, l_post, hl_split⟩ : ∃ s t, l = s ++ v_j :: t :=
          List.append_of_mem hv_j_mem
        have h_l_pre_ne : l_pre ≠ [] := by
          intro h_pre_nil
          rw [h_pre_nil, List.nil_append] at hl_split
          obtain ⟨h_head, _, _⟩ := h_fan
          rw [hl_split] at h_head
          simp only [List.head?_cons, Option.some.injEq] at h_head
          exact h_vj_ne_v h_head
        set v_jm1 := l_pre.getLast h_l_pre_ne with hv_jm1_def
        have h_vj_not_in_lpre : v_j ∉ l_pre := by
          obtain ⟨_, h_nodup_l, _⟩ := h_fan
          rw [hl_split, List.nodup_append'] at h_nodup_l
          intro h_in
          exact h_nodup_l.2.2 h_in List.mem_cons_self
        have hb_missing_vjm1 : b ∈ missingColors c v_jm1 := by
          obtain ⟨_, _, h_chain⟩ := h_fan
          rw [hl_split] at h_chain
          obtain ⟨_, _, h_boundary⟩ := List.isChain_append.mp h_chain
          have h_pre_last : v_jm1 ∈ l_pre.getLast? := by
            rw [List.getLast?_eq_some_getLast h_l_pre_ne]; rfl
          have h_post_head : v_j ∈ (v_j :: l_post).head? := rfl
          obtain ⟨e, he_val, he_col⟩ := h_boundary v_jm1 h_pre_last v_j h_post_head
          have h_e_eq_eb : e = e_b := by
            apply Subtype.ext
            rw [he_val, he_b_val]
          rw [h_e_eq_eb, he_b_col] at he_col
          exact he_col
        by_cases h_reach_jm1 : (kempeSubgraph c a b).Reachable u v_jm1
        · -- Sub-case B1(b): `v_{j-1}` reachable from `u`. Use the full fan.
          have h_c'_e_b : (swapKempe c a b u).toFun e_b = a := by
            rw [swapKempe_toFun_of_inSwapZone c a b u h_eb_inSZ, he_b_col,
                swapColors_b]
          have h_a_missing_vjm1_c' :
              a ∈ missingColors (swapKempe c a b u) v_jm1 := by
            intro h_inc
            obtain ⟨e', he'_inc, he'_col⟩ := h_inc
            by_cases h_swap : inSwapZone c a b u e'
            · rw [swapKempe_toFun_of_inSwapZone c a b u h_swap] at he'_col
              have h_c_e' : c.toFun e' = b := by
                apply swapColors_injective a b
                rw [he'_col, swapColors_b]
              exact hb_missing_vjm1 ⟨e', he'_inc, h_c_e'⟩
            · rw [swapKempe_toFun_of_not_inSwapZone c a b u h_swap] at he'_col
              exact h_swap ⟨Or.inl he'_col, v_jm1, he'_inc, h_reach_jm1⟩
          have h_vj_not_in_lpost : v_j ∉ l_post := by
            obtain ⟨_, h_nodup_l, _⟩ := h_fan
            rw [hl_split, List.nodup_append'] at h_nodup_l
            have h_nodup_post := h_nodup_l.2.1
            rw [List.nodup_cons] at h_nodup_post
            exact h_nodup_post.1
          have h_full_fan_c' : IsFan (swapKempe c a b u) u v l := by
            obtain ⟨h_head_l, h_nodup_l, h_chain_l⟩ := h_fan
            refine ⟨h_head_l, h_nodup_l, ?_⟩
            rw [hl_split] at h_chain_l
            obtain ⟨h_chain_pre_c, h_chain_post_c, _h_boundary_c⟩ :=
              List.isChain_append.mp h_chain_l
            rw [hl_split]
            refine List.IsChain.append ?_ ?_ ?_
            · apply h_chain_pre_c.imp_of_mem_imp
              intro a' b' _ha'_mem hb'_mem h_R_in_c
              obtain ⟨e, he_val, he_col⟩ := h_R_in_c
              refine ⟨e, he_val, ?_⟩
              have h_b'_ne_vj : b' ≠ v_j := fun h => h_vj_not_in_lpre (h ▸ hb'_mem)
              have h_c_e_ne_a : c.toFun e ≠ a := by
                intro h_col_a
                apply ha_u
                refine ⟨e, ?_, h_col_a⟩
                change u ∈ e.val
                rw [he_val]; exact Sym2.mem_mk_left u b'
              have h_c_e_ne_b : c.toFun e ≠ b := by
                intro h_col_b
                have h_u_in_e : u ∈ e.val := by
                  rw [he_val]; exact Sym2.mem_mk_left u b'
                have h_u_in_eb : u ∈ e_b.val := by
                  rw [he_b_val]; exact Sym2.mem_mk_left u v_j
                have h_e_eq_eb : e = e_b := by
                  by_contra h_ne_eb
                  exact c.valid ⟨h_ne_eb, u, h_u_in_e, h_u_in_eb⟩
                    (h_col_b.trans he_b_col.symm)
                have h_val_eq : e.val = e_b.val := h_e_eq_eb ▸ rfl
                rw [he_val, he_b_val, Sym2.eq_iff] at h_val_eq
                rcases h_val_eq with ⟨_, h_b'_eq_vj⟩ | ⟨h_u_eq_vj, _⟩
                · exact h_b'_ne_vj h_b'_eq_vj
                · exact h_u_ne_vj h_u_eq_vj
              have h_e_not_swap : ¬ inSwapZone c a b u e := by
                rintro ⟨h_col_swap, _⟩
                rcases h_col_swap with h | h
                · exact h_c_e_ne_a h
                · exact h_c_e_ne_b h
              rw [swapKempe_toFun_of_not_inSwapZone c a b u h_e_not_swap]
              exact (mem_missingColors_swapKempe_iff_of_ne c u a' h_c_e_ne_a h_c_e_ne_b).mpr he_col
            · apply h_chain_post_c.imp_of_mem_tail_imp
              intro a' b' _ha'_mem hb'_tail h_R_in_c
              have hb'_in_lpost : b' ∈ l_post := hb'_tail
              have h_b'_ne_vj : b' ≠ v_j := fun h =>
                h_vj_not_in_lpost (h ▸ hb'_in_lpost)
              obtain ⟨e, he_val, he_col⟩ := h_R_in_c
              refine ⟨e, he_val, ?_⟩
              have h_c_e_ne_a : c.toFun e ≠ a := by
                intro h_col_a
                apply ha_u
                refine ⟨e, ?_, h_col_a⟩
                change u ∈ e.val
                rw [he_val]; exact Sym2.mem_mk_left u b'
              have h_c_e_ne_b : c.toFun e ≠ b := by
                intro h_col_b
                have h_u_in_e : u ∈ e.val := by
                  rw [he_val]; exact Sym2.mem_mk_left u b'
                have h_u_in_eb : u ∈ e_b.val := by
                  rw [he_b_val]; exact Sym2.mem_mk_left u v_j
                have h_e_eq_eb : e = e_b := by
                  by_contra h_ne_eb
                  exact c.valid ⟨h_ne_eb, u, h_u_in_e, h_u_in_eb⟩
                    (h_col_b.trans he_b_col.symm)
                have h_val_eq : e.val = e_b.val := h_e_eq_eb ▸ rfl
                rw [he_val, he_b_val, Sym2.eq_iff] at h_val_eq
                rcases h_val_eq with ⟨_, h_b'_eq_vj⟩ | ⟨h_u_eq_vj, _⟩
                · exact h_b'_ne_vj h_b'_eq_vj
                · exact h_u_ne_vj h_u_eq_vj
              have h_e_not_swap : ¬ inSwapZone c a b u e := by
                rintro ⟨h_col_swap, _⟩
                rcases h_col_swap with h | h
                · exact h_c_e_ne_a h
                · exact h_c_e_ne_b h
              rw [swapKempe_toFun_of_not_inSwapZone c a b u h_e_not_swap]
              exact (mem_missingColors_swapKempe_iff_of_ne c u a' h_c_e_ne_a h_c_e_ne_b).mpr he_col
            · intro x hx y hy
              rw [List.getLast?_eq_some_getLast h_l_pre_ne] at hx
              change x ∈ some v_jm1 at hx
              change y ∈ some v_j at hy
              have hx_eq : x = v_jm1 := (Option.mem_some_iff.mp hx).symm
              have hy_eq : y = v_j := (Option.mem_some_iff.mp hy).symm
              subst hx_eq
              subst hy_eq
              refine ⟨e_b, he_b_val, ?_⟩
              rw [h_c'_e_b]
              exact h_a_missing_vjm1_c'
          exact IsFan.rotateTermA e_uv he_uv h_full_fan_c' h_ne b
            h_b_missing_u h_b_missing_vk
        · -- Sub-case B1(a): `v_{j-1}` unreachable. Use the shorter fan.
          have h_l_pre_fan_c' : IsFan (swapKempe c a b u) u v l_pre := by
            obtain ⟨h_head_l, h_nodup_l, h_chain_l⟩ := h_fan
            refine ⟨?_, ?_, ?_⟩
            · rw [hl_split] at h_head_l
              rwa [List.head?_append_of_ne_nil _ h_l_pre_ne] at h_head_l
            · rw [hl_split] at h_nodup_l
              exact (List.nodup_append'.mp h_nodup_l).1
            · rw [hl_split] at h_chain_l
              have h_chain_pre := (List.isChain_append.mp h_chain_l).1
              apply h_chain_pre.imp_of_mem_imp
              intro a' b' _ha'_mem hb'_mem h_R_in_c
              obtain ⟨e, he_val, he_col⟩ := h_R_in_c
              refine ⟨e, he_val, ?_⟩
              have h_c_e_ne_a : c.toFun e ≠ a := by
                intro h_col_a
                apply ha_u
                refine ⟨e, ?_, h_col_a⟩
                change u ∈ e.val
                rw [he_val]; exact Sym2.mem_mk_left u b'
              have h_b'_ne_vj : b' ≠ v_j := fun h => h_vj_not_in_lpre (h ▸ hb'_mem)
              have h_c_e_ne_b : c.toFun e ≠ b := by
                intro h_col_b
                have h_u_in_e : u ∈ e.val := by
                  rw [he_val]; exact Sym2.mem_mk_left u b'
                have h_u_in_eb : u ∈ e_b.val := by
                  rw [he_b_val]; exact Sym2.mem_mk_left u v_j
                have h_e_eq_eb : e = e_b := by
                  by_contra h_ne_eb
                  have h_lg_adj : (G.deleteEdges {e_uv.val}).lineGraph.Adj e e_b :=
                    ⟨h_ne_eb, u, h_u_in_e, h_u_in_eb⟩
                  exact c.valid h_lg_adj (h_col_b.trans he_b_col.symm)
                have h_val_eq : e.val = e_b.val := h_e_eq_eb ▸ rfl
                rw [he_val, he_b_val, Sym2.eq_iff] at h_val_eq
                rcases h_val_eq with ⟨_, h_b'_eq_vj⟩ | ⟨h_u_eq_vj, _⟩
                · exact h_b'_ne_vj h_b'_eq_vj
                · exact h_u_ne_vj h_u_eq_vj
              have h_e_not_swap : ¬ inSwapZone c a b u e := by
                rintro ⟨h_col_swap, _⟩
                rcases h_col_swap with h | h
                · exact h_c_e_ne_a h
                · exact h_c_e_ne_b h
              rw [swapKempe_toFun_of_not_inSwapZone c a b u h_e_not_swap]
              exact (mem_missingColors_swapKempe_iff_of_ne c u a' h_c_e_ne_a h_c_e_ne_b).mpr he_col
          have h_b_missing_vjm1_c' : b ∈ missingColors (swapKempe c a b u) v_jm1 := by
            rw [missingColors_swapKempe_of_not_reachable c a b u h_reach_jm1]
            exact hb_missing_vjm1
          exact IsFan.rotateTermA e_uv he_uv h_l_pre_fan_c' h_l_pre_ne b
            h_b_missing_u h_b_missing_vjm1_c'

/-- **Vizing's adjacency lemma.** A proper `(Δ+1)`-edge-coloring of `G − {e_uv}`
    extends to all of `G`, provided both endpoints of `e_uv` have missing colors
    and `u` has at least two missing colors.

    This is the key combinatorial lemma driving the inductive step in the proof
    of Vizing's theorem. -/
lemma vizingAdjacencyLemma
    [Fintype V] [Fintype α] [DecidableRel G.Adj]
    {u v : V} (e_uv : G.edgeSet) (he_uv : e_uv.val = s(u, v))
    (c : (G.deleteEdges {e_uv.val}).lineGraph.Coloring α)
    (h_missing_u : (missingColors c u).Nonempty)
    (h_missing_v : (missingColors c v).Nonempty)
    (h_card : G.maxDegree < Fintype.card α)
    (h_missing_u_card : 2 ≤ (missingColors c u).ncard) :
    Nonempty (G.lineGraph.Coloring α) := by
  classical
  -- Build an initial maximal fan from `u` rooted at `v`.
  obtain ⟨l, h_ne, h_fan, h_max⟩ := IsFan.exists_maximal (Fintype.card V)
    [v] (List.cons_ne_nil v []) (IsFan.singleton c u v) (by simp)
  exact vizingAdjacencyLemma_aux e_uv he_uv h_card c l h_ne h_fan h_max
    h_missing_u h_missing_v h_missing_u_card

end vizing
