/-
Copyright (c) 2024 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Turán density

This modules defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber (Fin n) H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.
-/


open Fintype Topology Asymptotics

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

section TuranDensity

/-- If `G` is an `n+1`-vertex `H`-free simple graph, then `n`-vertex induced subgraphs of `G` have
at most `extremalNumber (Fin n) H` number of edges. -/
lemma card_edgeFinset_induce_of_free_le_extremalNumber
    {n : ℕ} (G : SimpleGraph (Fin (n+1))) [DecidableRel G.Adj] (h : H.Free G) (x : Fin (n+1)) :
    (G.induce {x}ᶜ).edgeFinset.card ≤ extremalNumber (Fin n) H := by
  have h_card_eq : card (↑{x}ᶜ : Set (Fin (n+1))) = n := by
    simp_rw [←Set.toFinset_card, Set.toFinset_compl, Set.toFinset_singleton, Finset.card_compl,
      card_fin, Finset.card_singleton, Nat.add_sub_cancel]
  rw [←extremalNumber_eq_extremalNumber_of_iso (equivFinOfCardEq h_card_eq) Iso.refl]
  apply le_extremalNumber
  contrapose! h
  rw [not_not] at h ⊢
  exact h.trans ⟨SubgraphIso.induce G {x}ᶜ⟩

lemma extremalNumber_div_choose_two_succ_le {n : ℕ} (hn : 2 ≤ n) :
    (extremalNumber (Fin (n+1)) H / (n+1).choose 2 : ℝ)
      ≤ (extremalNumber (Fin n) H / n.choose 2 : ℝ) := by
  rw [div_le_iff₀ <| Nat.cast_pos.mpr <| Nat.choose_pos (by linarith),
    extremalNumber_le_iff_of_nonneg (Fin (n+1)) H (by positivity)]
  intro G _ h
  rw [mul_comm, ←mul_div_assoc, le_div_iff₀' <| Nat.cast_pos.mpr <| Nat.choose_pos hn]
  -- double-counting vertices not in edges
  let s := (Finset.univ ×ˢ G.edgeFinset).filter fun (v, e) ↦ v ∉ e
  -- counting over vertices
  have h_vertices : s.card ≤ extremalNumber (Fin n) H * (n+1) := by
    conv_rhs =>
      rw [←card_fin (n+1), ←Finset.card_univ, mul_comm, ←smul_eq_mul, ←Finset.sum_const]
    simp_rw [Finset.card_filter _ _, Finset.sum_product, ←Finset.card_filter]
    apply Finset.sum_le_sum
    simp_rw [Finset.mem_univ, forall_const, ←edgeFinset_deleteIncidenceSet_eq_filter,
      ←card_edgeFinset_induce_compl_singleton G]
    exact card_edgeFinset_induce_of_free_le_extremalNumber G h
  -- counting over edges
  have h_edges : s.card = G.edgeFinset.card * (n-1) := by
    simp_rw [Finset.card_filter _ _, Finset.sum_product_right, ←Finset.card_filter _ _,
      Sym2.mem_toFinset, Finset.filter_not, Finset.filter_mem_eq_inter,
      ←Finset.sum_attach G.edgeFinset, Finset.univ_inter, ←Finset.compl_eq_univ_sdiff,
      Finset.card_compl, card_fin, card_toFinset_mem_edgeFinset, Finset.sum_const,
      Finset.card_attach, smul_eq_mul, Nat.succ_sub_succ_eq_sub]
  rw [mul_comm (n.choose 2 : ℝ) _, Nat.cast_choose_two, ←mul_div_assoc,
    mul_comm ((n+1).choose 2 : ℝ) _, Nat.cast_choose_two, ←mul_div_assoc,
    div_le_div_iff_of_pos_right zero_lt_two, ←Nat.cast_pred (by positivity),
    ←Nat.cast_pred (by positivity), mul_comm (n : ℝ) _, ←mul_assoc, ←mul_assoc,
    show n + 1 - 1 = n from Nat.pred_succ n, mul_le_mul_right (by positivity), ←Nat.cast_mul,
    ←Nat.cast_mul, Nat.cast_le]
  rwa [h_edges] at h_vertices

/-- The limit `extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞` exists. -/
lemma exists_tendsto_extremalNumber_div_choose_two (H : SimpleGraph V) :
    ∃ x, Filter.Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      Filter.atTop (𝓝 x) := by
  let f := fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)
  suffices h : ∃ x, Filter.Tendsto (fun (n : ℕ) ↦ f (n + 2)) Filter.atTop (𝓝 x) by
    simpa [Filter.tendsto_add_atTop_iff_nat 2] using h
  -- limit of antitone sequence bounded from below is infimum
  use ⨅ n, f (n + 2)
  apply tendsto_atTop_ciInf
  · apply antitone_nat_of_succ_le
    intro n
    apply extremalNumber_div_choose_two_succ_le
    rw [le_add_iff_nonneg_left]
    exact Nat.zero_le n
  · simp_rw [bddBelow_def, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    use 0
    intro n
    positivity

/-- The **Turán density** of a simple graph `H` is the limit of
`extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph V) :=
  limUnder Filter.atTop
    fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ)

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph V) :
    Filter.Tendsto (fun (n : ℕ) ↦ (extremalNumber (Fin n) H / n.choose 2 : ℝ))
      Filter.atTop (𝓝 (turanDensity H)) := by
  have ⟨_, h⟩ := exists_tendsto_extremalNumber_div_choose_two H
  rwa [←Filter.Tendsto.limUnder_eq h] at h

/-- `extremalNumber (Fin n) H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
theorem isEquivalent_extremalNumber {H : SimpleGraph V} (h : turanDensity H ≠ 0) :
    (fun (n : ℕ) ↦ (extremalNumber (Fin n) H : ℝ))
      ~[Filter.atTop] (fun (n : ℕ) ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hz : ∀ᶠ (x : ℕ) in Filter.atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [Filter.eventually_atTop]
    use 2
    intro n hn
    field_simp [h, Nat.choose_eq_zero_iff, hn]
  rw [isEquivalent_iff_tendsto_one hz]
  have hπ := tendsto_turanDensity H
  apply Filter.Tendsto.const_mul (1 / (turanDensity H) : ℝ) at hπ
  simp_rw [one_div_mul_cancel h] at hπ
  convert hπ
  field_simp [Pi.div_apply]

end TuranDensity

end SimpleGraph
