/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

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

lemma bbdBelow_extremalNumber_div_choose_two (H : SimpleGraph W) :
    BddBelow { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := by
  refine ⟨0, fun x ⟨n, hn, hx⟩ ↦ ?_⟩
  rw [← hx]
  positivity

lemma tendsto_extremalNumber_div_choose_two (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop
      (𝓝 (sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 })) := by
  let f := fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)
  have hf_Ici : f '' (Set.Ici 2) = Set.range (fun n ↦ f (n + 2)) := by
    refine Set.ext fun x ↦ ⟨fun ⟨n, hn, hfn⟩ ↦ ⟨n - 2, ?_⟩, by grind⟩
    rwa [← Nat.sub_add_cancel hn] at hfn
  suffices h : Tendsto (fun n ↦ f (n + 2)) atTop (𝓝 (⨅ n, f (n + 2))) by
    rwa [tendsto_add_atTop_iff_nat 2, ← sInf_range, ← hf_Ici, Set.image] at h
  apply tendsto_atTop_ciInf
  · rw [antitone_add_nat_iff_antitoneOn_nat_Ici]
    exact antitoneOn_extremalNumber_div_choose_two H
  · rw [← hf_Ici, Set.image]
    exact bbdBelow_extremalNumber_div_choose_two H

/-- The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H / n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)

theorem turanDensity_eq_sInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  (tendsto_extremalNumber_div_choose_two H).limUnder_eq

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  rw [turanDensity_eq_sInf H]
  exact tendsto_extremalNumber_div_choose_two H

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
    ∃ N, ∀ {V : Type*} [Fintype V], N ≤ card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (turanDensity H + ε) * (card V).choose 2 → H ⊑ G := by
  have hπ := (turanDensity_eq_sInf H).ge
  contrapose! hπ with h
  apply lt_of_lt_of_le
  · exact lt_add_of_pos_right (turanDensity H) hε_pos
  · refine le_csInf ?_ (fun x ⟨n, hn, hx⟩ ↦ ?_)
    · rw [← Set.image, Set.image_nonempty]
      exact Set.nonempty_Ici
    · rw [← hx]
      have ⟨V, _, hcardV, G, _, hcard_edges, h_free⟩ := h n
      trans (extremalNumber (card V) H / (card V).choose 2)
      · rw [le_div_iff₀ <| mod_cast Nat.choose_pos (hn.trans hcardV)]
        exact hcard_edges.trans (mod_cast card_edgeFinset_le_extremalNumber h_free)
      · exact antitoneOn_extremalNumber_div_choose_two H hn (hn.trans hcardV) hcardV

end SimpleGraph
