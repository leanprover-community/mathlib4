/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Turán density

This files defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber (Fin n) H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.
-/


open Asymptotics Finset Fintype Topology

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

section TuranDensity

lemma extremalNumber_div_choose_two_succ_le {n : ℕ} (hn : 2 ≤ n) :
    (extremalNumber (Fin (n+1)) H / (n+1).choose 2 : ℝ)
      ≤ (extremalNumber (Fin n) H / n.choose 2 : ℝ) := by
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg (Fin (n+1)) H (by positivity)]
  intro G _ h
  rw [mul_comm, ←mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn)]
  -- double-counting vertices not in edges
  let s := (univ ×ˢ G.edgeFinset).filter fun (v, e) ↦ v ∉ e
  -- counting over vertices
  have h_vert : #s ≤ extremalNumber (Fin n) H * (n+1) := by
    rw [card_filter, sum_product]
    conv =>
      enter [1, 2, x]
      rw [←card_filter]
    conv_rhs =>
      rw [←Fintype.card_fin (n+1), ←card_univ, mul_comm, ←smul_eq_mul, ←sum_const]
    apply sum_le_sum; intro i _
    let e : ({i}ᶜ : Set (Fin (n+1))) ≃ Fin n := by
      apply Fintype.equivFinOfCardEq
      rw [Fintype.card_compl_set, Fintype.card_fin, card_unique]
      exact add_tsub_cancel_right n 1
    rw [←edgeFinset_deleteIncidenceSet_eq_filter, ←card_edgeFinset_induce_compl_singleton,
      ←extremalNumber_eq_extremalNumber_of_iso e Iso.refl]
    apply le_extremalNumber
    contrapose! h
    rw [not_not] at h ⊢
    exact h.trans ⟨SubgraphIso.induce G {i}ᶜ⟩
  -- counting over edges
  have h_edge : #s = #G.edgeFinset * (n-1) := by
    rw [card_filter, sum_product_right]
    conv =>
      enter [1, 2, y]
      rw [←card_filter]
    simp_rw [Sym2.mem_toFinset, filter_not, filter_mem_eq_inter, ←sum_attach G.edgeFinset,
      univ_inter, ←compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset,
      sum_const, card_attach, smul_eq_mul, Nat.succ_sub_succ_eq_sub]
  rw [mul_comm (n.choose 2 : ℝ) _, Nat.cast_choose_two, ←mul_div_assoc,
    mul_comm ((n+1).choose 2 : ℝ) _, Nat.cast_choose_two, ←mul_div_assoc,
    div_le_div_iff_of_pos_right zero_lt_two, ←Nat.cast_pred (by positivity),
    ←Nat.cast_pred (by positivity), mul_comm (n : ℝ) _, ←mul_assoc, ←mul_assoc,
    add_tsub_cancel_right n 1, mul_le_mul_right (by positivity)]
  rw [h_edge] at h_vert; assumption_mod_cast

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
  · simp_rw [bddBelow_def, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    use 0; intro n
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
    use 2; intro n hn
    simp [h, Nat.choose_eq_zero_iff, hn]
  rw [isEquivalent_iff_tendsto_one hz]
  have hπ := tendsto_turanDensity H
  apply Filter.Tendsto.const_mul (1 / (turanDensity H) : ℝ) at hπ
  simp_rw [one_div_mul_cancel h] at hπ
  convert hπ
  field_simp [Pi.div_apply]

end TuranDensity

end SimpleGraph
