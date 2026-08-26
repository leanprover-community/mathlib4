/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VizingFan.Basic

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

/-! ### Term-A: Fan Rotation Extending the Coloring -/

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- Induction on fan length for `rotateTermA`. -/
private lemma rotateTermA_aux
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u v : V) (e_uv : G.edgeSet) (he_uv : e_uv.val = s(u, v)) :
    ∀ (n : ℕ) (c : (G.deleteEdges {e_uv.val}).lineGraph.Coloring α)
      (l : List V) (h_ne : l ≠ []) (_h_len : l.length = n + 1)
      (_ : IsFan c u v l)
      (γ : α)
      (_ : γ ∈ missingColors c u)
      (_ : γ ∈ missingColors c (l.getLast h_ne)),
    Nonempty (G.lineGraph.Coloring α) := by
  intro n
  induction n with
  | zero =>
    -- Base case: l = [v₀], so γ is free at both u and v₀.
    intro c l h_ne h_len h_fan γ h_γ_u h_γ_vk
    obtain ⟨v_only, rfl⟩ := List.length_eq_one_iff.mp h_len
    obtain ⟨h_head, _, _⟩ := h_fan
    simp only [List.head?_cons, Option.some.injEq] at h_head
    subst v_only
    apply extendColoring_of_missingColors_both e_uv he_uv c γ h_γ_u
    simpa using h_γ_vk
  | succ k ih =>
    intro c l h_ne h_len h_fan γ h_γ_u h_γ_vk
    -- l has length k + 2 ≥ 2.
    have h_l_dl_len : l.dropLast.length = k + 1 := by
      rw [List.length_dropLast]; omega
    have h_l_dl_ne : l.dropLast ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil] at h_l_dl_len
      omega
    set v_k := l.getLast h_ne with hv_k_def
    set v_km1 := l.dropLast.getLast h_l_dl_ne with hv_km1_def
    -- Extract the last fan edge `e_k` (between u and v_k) whose color is
    -- missing at v_{k-1}.
    have h_last_edge : ∃ e_k : (G.deleteEdges {e_uv.val}).edgeSet,
        e_k.val = s(u, v_k) ∧ c.toFun e_k ∈ missingColors c v_km1 := by
      obtain ⟨_, _, h_chain⟩ := h_fan
      have h_decomp : l.dropLast ++ [v_k] = l :=
        List.dropLast_append_getLast h_ne
      have h_chain' : (l.dropLast ++ [v_k]).IsChain
          (fun a b => ∃ e : (G.deleteEdges {e_uv.val}).edgeSet,
              e.val = s(u, b) ∧ c.toFun e ∈ missingColors c a) := by
        rw [h_decomp]; exact h_chain
      obtain ⟨_, _, h_rel⟩ := List.isChain_append.mp h_chain'
      have h_dl_last_mem : v_km1 ∈ l.dropLast.getLast? := by
        rw [List.getLast?_eq_some_getLast h_l_dl_ne]
        exact rfl
      exact h_rel v_km1 h_dl_last_mem v_k rfl
    obtain ⟨e_k, he_k_val, he_k_col⟩ := h_last_edge
    let c_k := c.toFun e_k
    -- Recolor `e_k` from `c_k` to `γ`.
    obtain ⟨c'', h_c''_e_k, h_c''_other⟩ :=
      recolorEdge_of_missingColors c e_k he_k_val γ h_γ_u h_γ_vk
    have h_vk_not_in_dl : v_k ∉ l.dropLast := by
      obtain ⟨_, h_nodup, _⟩ := h_fan
      intro hmem
      have h_decomp : l.dropLast ++ [v_k] = l := List.dropLast_append_getLast h_ne
      have h_nodup' : (l.dropLast ++ [v_k]).Nodup := by rw [h_decomp]; exact h_nodup
      rw [List.nodup_append'] at h_nodup'
      exact h_nodup'.2.2 hmem (List.mem_singleton.mpr rfl)
    have h_u_ne_vk : u ≠ v_k := by
      have h_adj : (G.deleteEdges {e_uv.val}).Adj u v_k := by
        have hp := e_k.property
        rw [he_k_val] at hp
        exact (SimpleGraph.mem_edgeSet _).mp hp
      exact h_adj.ne
    -- `l.dropLast` is a fan in `c''`.
    have h_smaller_fan : IsFan c'' u v l.dropLast := by
      obtain ⟨h_head_l, h_nodup_l, h_chain_l⟩ := h_fan
      refine ⟨?_, ?_, ?_⟩
      · rcases l with _ | ⟨a, rest⟩
        · exact absurd rfl h_ne
        · rcases rest with _ | ⟨b, rest'⟩
          · simp at h_len
          · simp only [List.head?_cons, Option.some_inj] at h_head_l
            subst a
            rfl
      · have h_decomp_l : l.dropLast ++ [v_k] = l := List.dropLast_append_getLast h_ne
        have h_nodup' : (l.dropLast ++ [v_k]).Nodup := by rw [h_decomp_l]; exact h_nodup_l
        exact (List.nodup_append'.mp h_nodup').1
      · have h_decomp_l : l.dropLast ++ [v_k] = l := List.dropLast_append_getLast h_ne
        have h_chain_form : (l.dropLast ++ [v_k]).IsChain
            (fun a b => ∃ e : (G.deleteEdges {e_uv.val}).edgeSet,
                e.val = s(u, b) ∧ c.toFun e ∈ missingColors c a) := by
          rw [h_decomp_l]; exact h_chain_l
        have h_chain_dl := (List.isChain_append.mp h_chain_form).1
        apply h_chain_dl.imp_of_mem_imp
        intro a b _ha_mem hb_mem hab
        obtain ⟨e, he_val, he_col⟩ := hab
        refine ⟨e, he_val, ?_⟩
        have h_b_ne_vk : b ≠ v_k := fun h => h_vk_not_in_dl (h ▸ hb_mem)
        have h_e_ne_ek : e ≠ e_k := by
          intro h_eq
          apply h_b_ne_vk
          have h_val_eq : e.val = e_k.val := by rw [h_eq]
          rw [he_val, he_k_val, Sym2.eq_iff] at h_val_eq
          rcases h_val_eq with ⟨_, h⟩ | ⟨h_uvk, _⟩
          · exact h
          · exact absurd h_uvk h_u_ne_vk
        rw [h_c''_other e h_e_ne_ek]
        intro h_inc
        obtain ⟨e₂, he₂_inc, he₂_col⟩ := h_inc
        by_cases h_e₂ : e₂ = e_k
        · rw [h_e₂, h_c''_e_k] at he₂_col
          apply h_γ_u
          refine ⟨e, ?_, he₂_col.symm⟩
          change u ∈ e.val
          rw [he_val]
          exact Sym2.mem_mk_left u b
        · rw [h_c''_other e₂ h_e₂] at he₂_col
          exact he_col ⟨e₂, he₂_inc, he₂_col⟩
    -- `c_k` is missing at `u` in `c''`.
    have h_c_k_missing_u : c_k ∈ missingColors c'' u := by
      intro h_inc
      obtain ⟨e', he'_inc, he'_col⟩ := h_inc
      by_cases h_e' : e' = e_k
      · rw [h_e', h_c''_e_k] at he'_col
        apply h_γ_u
        refine ⟨e_k, ?_, he'_col.symm⟩
        change u ∈ e_k.val
        rw [he_k_val]; exact Sym2.mem_mk_left u v_k
      · rw [h_c''_other e' h_e'] at he'_col
        have h_e_k_at_u : u ∈ e_k.val := by
          rw [he_k_val]; exact Sym2.mem_mk_left u v_k
        have h_lg_adj : (G.deleteEdges {e_uv.val}).lineGraph.Adj e_k e' :=
          ⟨fun h => h_e' h.symm, u, h_e_k_at_u, he'_inc⟩
        have h_diff : c.toFun e_k ≠ c.toFun e' := c.valid h_lg_adj
        apply h_diff
        rw [he'_col]
    -- `c_k` is missing at `v_{k-1}` in `c''`.
    have h_c_k_missing_vkm1 : c_k ∈ missingColors c'' v_km1 := by
      intro h_inc
      obtain ⟨e', he'_inc, he'_col⟩ := h_inc
      by_cases h_e' : e' = e_k
      · rw [h_e', h_c''_e_k] at he'_col
        apply h_γ_u
        refine ⟨e_k, ?_, he'_col.symm⟩
        change u ∈ e_k.val
        rw [he_k_val]; exact Sym2.mem_mk_left u v_k
      · rw [h_c''_other e' h_e'] at he'_col
        exact he_k_col ⟨e', he'_inc, he'_col⟩
    exact ih c'' l.dropLast h_l_dl_ne h_l_dl_len h_smaller_fan c_k
      h_c_k_missing_u h_c_k_missing_vkm1

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Fan rotation (Term-A).** If `γ` is missing at both `u` and the last
    fan vertex, the partial coloring extends to all of `G`.

    The proof proceeds by induction on the fan length: each step recolors
    the last fan edge to `γ`, shortening the fan and producing a new free
    color for the next step. -/
lemma IsFan.rotateTermA
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} (e_uv : G.edgeSet) (he_uv : e_uv.val = s(u, v))
    {c : (G.deleteEdges {e_uv.val}).lineGraph.Coloring α}
    {l : List V} (h_fan : IsFan c u v l) (h_ne : l ≠ [])
    (γ : α)
    (h_γ_u : γ ∈ missingColors c u)
    (h_γ_vk : γ ∈ missingColors c (l.getLast h_ne)) :
    Nonempty (G.lineGraph.Coloring α) := by
  have h_len : l.length = (l.length - 1) + 1 := by
    have : 0 < l.length := List.length_pos_iff.mpr h_ne
    omega
  exact rotateTermA_aux u v e_uv he_uv (l.length - 1) c l h_ne h_len h_fan γ
    h_γ_u h_γ_vk


end vizing
