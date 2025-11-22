/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset` is the proof that `n`-vertex simple graphs having
  at least `(turanDensity H + o(1)) * n ^ 2` edges contain `H`, for sufficently large `n`.
-/

@[expose] public section


open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n+1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n-1 : ℝ), ← mul_div (n-1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc, mul_comm (n-1 : ℝ),
    ← mul_div (n+1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc, mul_le_mul_iff_right₀ (by positivity),
    ← Nat.cast_pred (by positivity), ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_mul, Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n+1), ← card_univ]
  -- double counting `(v, e) ↦ v ∉ e`
  apply card_nsmul_le_card_nsmul' (r := fun v e ↦ v ∉ e)
  -- counting `e`
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  -- counting `v`
  · intro v hv
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using card_edgeFinset_deleteIncidenceSet_le_extremalNumber h v

/-- The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H / n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)

theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } (turanDensity H) := by
  apply Real.isGLB_limUnder_of_bddBelow_antitoneOn_Ici
  · refine ⟨0, fun x ⟨_, _, hx⟩ ↦ ?_⟩
    rw [← hx]
    positivity
  · exact antitoneOn_extremalNumber_div_choose_two H

theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  have h_tendsto := Real.tendsto_csInf_of_bddBelow_antitoneOn_Ici
    (isGLB_turanDensity H).bddBelow (antitoneOn_extremalNumber_div_choose_two H)
  rwa [turanDensity, h_tendsto.limUnder_eq]

/-- `extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
theorem isEquivalent_extremalNumber (h : turanDensity H ≠ 0) :
    (fun n ↦ (extremalNumber n H : ℝ)) ~[atTop] (fun n ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1/turanDensity H : ℝ) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn ↦ ?_⟩
    simp [h, Nat.choose_eq_zero_iff, hn]
  simpa [isEquivalent_iff_tendsto_one hz] using hπ

/-- `n`-vertex simple graphs having at least `(turanDensity H + o(1)) * n ^ 2` edges contain
`H`, for sufficently large `n`. -/
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G := by
  have hπ := (turanDensity_eq_csInf H).ge
  contrapose! hπ with h
  apply lt_of_lt_of_le
  · exact lt_add_of_pos_right (turanDensity H) hε_pos
  · refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ ↦ ?_)
    · rw [← Set.image, Set.image_nonempty]
      exact Set.nonempty_Ici
    · rw [← hx]
      have ⟨n, hn, G, _, hcard_edges, h_free⟩ := h m
      replace h_free : H.Free G := by rwa [← not_nonempty_iff] at h_free
      trans (extremalNumber n H / n.choose 2)
      · rw [le_div_iff₀ <| mod_cast Nat.choose_pos (hm.trans hn)]
        conv =>
          enter [2, 1, 1]
          rw [← Fintype.card_fin n]
        exact hcard_edges.trans (mod_cast card_edgeFinset_le_extremalNumber h_free)
      · exact antitoneOn_extremalNumber_div_choose_two H hm (hm.trans hn) hn

end SimpleGraph
