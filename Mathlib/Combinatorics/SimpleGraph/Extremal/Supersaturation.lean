/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
public import Mathlib.Combinatorics.SimpleGraph.Finite

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Supersaturation

This file proves the **supersaturation theorem** for simple graphs.

## Main statements

* `SimpleGraph.eventually_labelledCopyCount_ge_of_card_edgeFinset` is the **supersaturation
  theorem**: if `ε > 0` and `H` is a simple graph, then for all sufficiently large `n`, every simple
  graph `G` on `Fin n` with at least `(turanDensity H + ε) * n.choose 2` edges contains at least
  `supersaturationConst H ε * n ^ v(H)` labelled copies of `H`, where `supersaturationConst H ε` is
  an explicit positive constant depending only on `H` and `ε`.
-/

@[expose] public section


open Filter Finset Fintype Function

namespace SimpleGraph

variable {W : Type*} {H : SimpleGraph W} {n : ℕ} {ε : ℝ}

open scoped Classical in
/-- `turanDenseGraphs n H ε` is the finset of simple graphs on `Fin n` having an edge density of at
least `turanDensity H + ε`. -/
noncomputable abbrev turanDenseGraphs (n : ℕ) (H : SimpleGraph W) (ε : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  { F : SimpleGraph (Fin n) | ∃ _ : DecidableRel F.Adj,
    #F.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 }

lemma top_mem_turanDenseGraphs (h : H.turanDensity + ε ≤ 1) :
    ⊤ ∈ turanDenseGraphs n H ε := by classical
  refine (mem_filter_univ ⊤).mpr ⟨inferInstance, ?_⟩
  rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin n, ge_iff_le]
  exact mul_le_of_le_one_left (Nat.cast_nonneg _) h

theorem turanDenseGraphs_nonempty (h : H.turanDensity + ε ≤ 1) :
    (turanDenseGraphs n H ε).Nonempty :=
  ⟨⊤, top_mem_turanDenseGraphs h⟩

variable {G : SimpleGraph (Fin n)}

/-- `turanDenseSubsets G k H ε` is the finset of `k`-sized finsets of vertices whose induced
subgraphs `G.induce s` have an edge density of at least `turanDensity H + ε`. -/
noncomputable abbrev turanDenseSubsets (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (H : SimpleGraph W) (ε : ℝ) : Finset (Finset (Fin n)) :=
  { s ∈ univ.powersetCard k | #(G.induce s).edgeFinset ≥ (turanDensity H + ε) * k.choose 2 }

/-- The number of `k`-sized finsets of vertices in `turanDenseSubsets` is at least a positive
proportion of all `k`-sized finsets of vertices. -/
theorem le_card_turanDenseSubsets [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k) (hε_pos : 0 < ε)
    (h : #G.edgeFinset ≥ (H.turanDensity + ε) * n.choose 2) :
    ε / 2 * n.choose k ≤ #(turanDenseSubsets G k H (ε / 2)) := by
  -- double count the `k`-sized sets with induced subgraphs that have sufficient edges
  set S := turanDenseSubsets G k H (ε / 2)
  have hS_subset : S ⊆ univ.powersetCard k := filter_subset _ _
  have hS : #G.edgeFinset * (n - 2).choose (k - 2) ≤ #S * k.choose 2
      + (n.choose k - #S) * (H.turanDensity + ε / 2) * k.choose 2 := by classical
    -- double count `(s, e)` where `s` is a `k`-sized subset containing the vertices of `e`
    let T := (univ.powersetCard k ×ˢ G.edgeFinset).filter fun (s, e) ↦ e.toFinset ⊆ s
    trans (#T : ℝ)
    · have he {e : G.edgeFinset} := hk.trans_eq' (card_toFinset_mem_edgeFinset e).symm
      simp_rw [T, card_filter, sum_product_right, ← card_filter, ← sum_attach G.edgeFinset,
        card_filter_powersetCard_subset _ _ _ (subset_univ _) he, card_univ,
        card_toFinset_mem_edgeFinset, sum_const, smul_eq_mul, card_attach, Nat.cast_mul,
        Fintype.card_fin, le_rfl]
    · simp_rw [T, card_filter, sum_product, ← card_filter,
        card_filter_edgeFinset_toFinset_subset, ← sum_inter_add_sum_sdiff (univ.powersetCard k) S,
        inter_eq_right.mpr hS_subset, Nat.cast_add]
      refine add_le_add ?_ ?_
      · rw [← Nat.cast_mul, Nat.cast_le, ← smul_eq_mul]
        exact sum_le_card_nsmul _ _ _ fun s hs ↦ card_edgeFinset_le_card_choose_two.trans_eq
          (by rw [← Set.toFinset_card, toFinset_coe, mem_powersetCard_univ.mp (hS_subset hs)])
      · push_cast
        refine (sum_le_card_nsmul _ _ ((H.turanDensity + ε / 2) * k.choose 2)
          fun s hs ↦ ?_).trans_eq ?_
        · obtain ⟨hs, nhs⟩ := mem_sdiff.mp hs
          rw [mem_filter, not_and, ge_iff_le, not_le] at nhs
          exact (nhs hs).le
        · rw [nsmul_eq_mul, card_sdiff_of_subset hS_subset,
            Nat.cast_sub (card_le_card hS_subset), card_powersetCard, card_univ,
            Fintype.card_fin, ← mul_assoc]
  -- solve for `#S` using the bound on the number of edges of `G`
  have h_choose_mul : (n.choose 2 : ℝ) * (n - 2).choose (k - 2) = (n.choose k : ℝ) * k.choose 2 :=
    mod_cast (Nat.choose_mul hk).symm
  have h_choose_pos : (0 : ℝ) < k.choose 2 := mod_cast Nat.choose_pos hk
  replace hS : (H.turanDensity + ε) * ((n.choose k : ℝ) * k.choose 2)
      ≤ #S * k.choose 2 + ((n.choose k : ℝ) - #S) * (H.turanDensity + ε / 2) * k.choose 2 := by
    refine hS.trans' ?_
    rw [← h_choose_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have h_nonneg : (0 : ℝ) ≤ #S * ((H.turanDensity + ε / 2) * k.choose 2) :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (add_nonneg (turanDensity_nonneg H) (half_pos hε_pos).le) (Nat.cast_nonneg _))
  nlinarith [hS, h_choose_pos, h_nonneg]

variable [Fintype W]

/-- `turanDenseGraphs.minLabelledCopyCount n H ε` is the minimum number of labelled copies of `H`
in any simple graph in `turanDenseGraphs n H ε`.

Note that this value is `0` if `turanDenseGraphs n H ε` is empty. -/
noncomputable abbrev turanDenseGraphs.minLabelledCopyCount (n : ℕ) (H : SimpleGraph W) (ε : ℝ) :=
  WithTop.untopD 0 <| (turanDenseGraphs n H ε).inf (labelledCopyCount · H)

theorem turanDenseGraphs.minLabelledCopyCount_eq_inf' (h : H.turanDensity + ε ≤ 1) :
    turanDenseGraphs.minLabelledCopyCount n H ε
      = (turanDenseGraphs n H ε).inf' (turanDenseGraphs_nonempty h) (labelledCopyCount · H) :=
  WithTop.untopD_eq_iff.mpr <| Or.inl <| Eq.symm <| coe_inf' (turanDenseGraphs_nonempty h) _

/-- The minimum number of labelled copies of `H` in any simple graph in `turanDenseGraphs` is
positive, given
at least `turanDensityConst H ε` many vertices. -/
theorem turanDenseGraphs.minLabelledCopyCount_pos (hε_pos : 0 < ε)
    (h_verts : turanDensityConst H ε ≤ n) (h : H.turanDensity + ε ≤ 1) :
    0 < turanDenseGraphs.minLabelledCopyCount n H ε := by
  simp_rw [turanDenseGraphs.minLabelledCopyCount_eq_inf' h, lt_inf'_iff,
    mem_filter_univ, forall_exists_index, labelledCopyCount_pos]
  exact fun F _ hF ↦ isContained_of_card_edgeFinset H hε_pos
    (by simpa using h_verts) F (by simpa using hF)

/-- Each simple graph in `turanDenseSubsets` contains at least
`turanDenseGraphs.minLabelledCopyCount k H ε` labelled copies of `H`, and each labelled copy of `H`
in `G` lies in at most `(n - card W).choose (k - card W)` of the `k`-sized finsets of vertices. -/
theorem turanDenseGraphs.minLabelledCopyCount_mul_card_turanDenseSubsets_le [DecidableRel G.Adj]
    {k : ℕ} (hcard : card W ≤ k) (h : H.turanDensity + ε ≤ 1) :
    turanDenseGraphs.minLabelledCopyCount k H ε * #(turanDenseSubsets G k H ε)
      ≤ G.labelledCopyCount H * (n - card W).choose (k - card W) := by classical
  -- double count `(s, f)` where `s` is a `k`-sized subset containing the image of `f`
  let T := (univ.powersetCard k ×ˢ univ).filter fun (s, (f : Copy H G)) ↦ univ.map f.toEmbedding ⊆ s
  trans #T
  · simp_rw [T, card_filter, sum_product, mul_sum]
    refine sum_le_sum (fun s hs ↦ ?_)
    classical rw [← card_filter, mul_ite, mul_one, mul_zero,
      ← labelledCopyCount_induce_eq_card_filter_copy s]
    split_ifs with hcard_edges
    · have : Nonempty (s ≃ Fin k) := by
        simp_rw [← card_eq, card_coe, Fintype.card_fin, mem_powersetCard_univ.mp hs]
      let f : s ≃ Fin k := Classical.arbitrary (s ≃ Fin k)
      have hf : (G.induce s).map f.toEmbedding ∈ turanDenseGraphs k H ε := by
        simp_rw [mem_filter_univ]
        refine ⟨inferInstance, ?_⟩
        rw [(G.induce s).card_edgeFinset_map f.toEmbedding, ge_iff_le]
        exact hcard_edges.le.trans_eq (mod_cast by convert rfl)
      simp_rw [turanDenseGraphs.minLabelledCopyCount_eq_inf' h, inf'_le_iff]
      exact ⟨(G.induce s).map f, hf,
        by rw [← labelledCopyCount_congr_left (Iso.map f _)]⟩
    · exact Nat.zero_le _
  · have hf {f : Copy H G} : #(univ.map f.toEmbedding) ≤ k := by
      rwa [← card_univ, ← card_map f.toEmbedding] at hcard
    classical simp_rw [T, card_filter, sum_product_right, ← card_filter,
      card_filter_powersetCard_subset _ _ _ (subset_univ _) hf, card_map, card_univ,
      Fintype.card_fin, sum_const, smul_eq_mul, card_univ, labelledCopyCount_eq_card_copy, le_rfl]

/-- Simple graphs on sufficiently many vertices `n` having at least
`(turanDensity H + ε) * n.choose 2` many edges contain at least
`supersaturationConst H ε * n ^ (card W)` labelled copies of `H`.

Note that this value is only defined for positive `ε` and `supersaturationConst H ε = 0` for non
positive `ε`. -/
noncomputable abbrev supersaturationConst (H : SimpleGraph W) (ε : ℝ) : ℝ :=
  if ε > 0 then
    turanDenseGraphs.minLabelledCopyCount (turanDensityConst H (ε / 2)) H (ε / 2) * (ε / 2)
      / (turanDensityConst H (ε / 2)).choose (card W) / (2 ^ card W * (card W).factorial)
  else 0

/-- The supersaturation theorem constant is positive, for positive `ε` such that
`turanDensity H + ε / 2 ≤ 1`. -/
theorem supersaturationConst_pos (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    (h : H.turanDensity + ε / 2 ≤ 1) : 0 < supersaturationConst H ε := by
  simp_rw [supersaturationConst, if_pos hε_pos]
  refine div_pos (div_pos (mul_pos ?_ (half_pos hε_pos)) ?_) (by positivity)
  · exact_mod_cast turanDenseGraphs.minLabelledCopyCount_pos (half_pos hε_pos) le_rfl h
  · exact_mod_cast Nat.choose_pos (card_le_turanDensityConst H (half_pos hε_pos) h)

/-- If `G` has sufficiently many vertices `n` and at least `(turanDensity H + ε) * n.choose 2`
many edges, then `G` contains at least `supersaturationConst H ε * n ^ v(H)` labelled copies of
`H`.

This is the **supersaturation theorem** for simple graphs. -/
theorem eventually_labelledCopyCount_ge_of_card_edgeFinset {ε : ℝ} (hε_pos : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 →
        G.labelledCopyCount H ≥ supersaturationConst H ε * n ^ card W := by
  rcases lt_or_ge 1 (turanDensity H + ε) with hπH_ε | hπH_ε
  -- if `turanDensity H + ε > 1` then no simple graph has sufficiently many edges
  · refine eventually_atTop.mpr ⟨2, fun n hn {G} _ hcard_edges ↦ absurd hcard_edges ?_⟩
    push Not
    have h_le : #G.edgeFinset ≤ n.choose 2 := by
      simpa using card_edgeFinset_le_card_choose_two (G := G)
    exact lt_of_le_of_lt (mod_cast h_le) <| lt_mul_left (mod_cast Nat.choose_pos hn) hπH_ε
  · have hπH_halfε : turanDensity H + ε / 2 < 1 := by linarith
    simp_rw [supersaturationConst, if_pos hε_pos]
    -- `k` is large enough that every `F ∈ turanDenseGraphs` contains `H`
    set k := turanDensityConst H (ε / 2)
    have hcardW_le_k : card W ≤ k := card_le_turanDensityConst H (half_pos hε_pos) hπH_halfε.le
    set c := turanDenseGraphs.minLabelledCopyCount k H (ε / 2) with hc_def
    set δ' := c * (ε / 2) / k.choose (card W) with hδ'_def
    rcases lt_or_ge (card W) 2 with hcardW | hcardW
    · -- if `card W ≤ 1` then `H` is the empty graph and copies are just vertex injections
      have hH : H = ⊥ := by
        have : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        ext a b
        simpa using fun hab ↦ hab.ne (Subsingleton.elim a b)
      -- the constant is at most `1`
      have hc_le : c ≤ (card W).factorial * k.choose (card W) := by
        rw [hc_def, turanDenseGraphs.minLabelledCopyCount_eq_inf' hπH_halfε.le,
          ← Nat.descFactorial_eq_factorial_mul_choose]
        apply le_of_le_of_eq <| inf'_le _ <| top_mem_turanDenseGraphs hπH_halfε.le
        rw [hH, labelledCopyCount_bot, Fintype.card_fin]
      have hδ'_le_one : δ' / (2 ^ card W * (card W).factorial) ≤ 1 := by
        rw [hδ'_def, div_div,
          div_le_one <| mul_pos (mod_cast Nat.choose_pos hcardW_le_k) (by positivity)]
        have hc_le' : (c : ℝ) ≤ (card W).factorial * k.choose (card W) := mod_cast hc_le
        have hε2 : ε / 2 ≤ 1 := by linarith [turanDensity_nonneg H]
        have h2pow : (1 : ℝ) ≤ 2 ^ card W := one_le_pow₀ one_le_two
        calc (c : ℝ) * (ε / 2)
            ≤ ((card W).factorial * k.choose (card W) : ℝ) * 1 := by gcongr
          _ = (k.choose (card W) : ℝ) * (1 * (card W).factorial) := by ring
          _ ≤ (k.choose (card W) : ℝ) * (2 ^ card W * (card W).factorial) := by gcongr
      refine Eventually.of_forall fun n G _ _ ↦ ?_
      have hcount : (G.labelledCopyCount H : ℝ) = n ^ card W := by
        rw [hH, labelledCopyCount_bot, Fintype.card_fin]
        rcases (by omega : card W = 0 ∨ card W = 1) with h | h <;> simp [h]
      rw [ge_iff_le, hcount]
      exact mul_le_of_le_one_left (by positivity) hδ'_le_one
    have hk_2 : 2 ≤ k := hcardW.trans hcardW_le_k
    -- the minimum number of copies of `H` in any `F ∈ turanDenseGraphs` is positive
    have hc_pos : 0 < c :=
      turanDenseGraphs.minLabelledCopyCount_pos (half_pos hε_pos) le_rfl hπH_halfε.le
    have hδ'_pos : 0 < δ' :=
      div_pos (mul_pos (mod_cast hc_pos) (half_pos hε_pos)) (mod_cast Nat.choose_pos hcardW_le_k)
    -- `n ^ card W / (2 ^ card W * (card W)!)` is less than `n.choose (card W)`
    have hpow_le_choose : ∀ n : ℕ, 2 * card W ≤ n →
        (n : ℝ) ^ card W / (2 ^ card W * (card W).factorial) ≤ n.choose (card W) := by
      intro n hn
      have hn' : (n : ℝ) / 2 ≤ ((n + 1 - card W : ℕ) : ℝ) := by
        have : 2 * (card W : ℝ) ≤ n := by exact_mod_cast hn
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      calc (n : ℝ) ^ card W / (2 ^ card W * (card W).factorial)
          = ((n : ℝ) / 2) ^ card W / (card W).factorial := by
            rw [← div_div, ← div_pow]
        _ ≤ ((n + 1 - card W : ℕ) : ℝ) ^ card W / (card W).factorial := by gcongr
        _ ≤ n.choose (card W) := Nat.pow_le_choose (card W) n
    refine eventually_atTop.mpr ⟨max k (2 * card W), fun n hn G _ hcard_edges ↦ ?_⟩
    have hk_n : k ≤ n := (le_max_left k (2 * card W)).trans hn
    -- there are at least `δ' * n.choose (card W)` copies of `H` in `G`
    have h : δ' * n.choose (card W) ≤ G.labelledCopyCount H := by
      have h_choose_mul : (n.choose (card W) : ℝ)
          = n.choose k / (n - card W).choose (k - card W) * k.choose (card W) := by
        rw [div_mul_eq_mul_div,
          eq_div_iff_mul_eq (mod_cast Nat.choose_ne_zero (Nat.sub_le_sub_right hk_n (card W)))]
        exact_mod_cast (Nat.choose_mul hcardW_le_k).symm
      rw [h_choose_mul, mul_rotate', mul_div_cancel₀ _ (mod_cast Nat.choose_ne_zero hcardW_le_k),
        div_mul_eq_mul_div, mul_comm,
        div_le_iff₀ (mod_cast Nat.choose_pos (Nat.sub_le_sub_right hk_n (card W)))]
      trans c * #(turanDenseSubsets G k H (ε / 2))
      · rw [mul_assoc, mul_le_mul_iff_right₀ (mod_cast hc_pos)]
        exact le_card_turanDenseSubsets hk_2 hε_pos hcard_edges
      · norm_cast
        exact turanDenseGraphs.minLabelledCopyCount_mul_card_turanDenseSubsets_le hcardW_le_k
          hπH_halfε.le
    rw [ge_iff_le, div_mul_eq_mul_div, mul_div_assoc]
    exact h.trans' <| mul_le_mul_of_nonneg_left
      (hpow_le_choose n <| hn.trans' <| le_max_right k (2 * card W)) hδ'_pos.le

end SimpleGraph
