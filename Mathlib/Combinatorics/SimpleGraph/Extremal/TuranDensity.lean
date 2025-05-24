/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Turán density

This files defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.
-/


open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- If `G` is `H.Free`, then `G.deleteIncidenceSet v` is also `H.Free` and has at most
`extremalNumber (card V-1) H` many edges. -/
theorem card_edgeFinset_deleteIncidenceSet_le_extremalNumber
    [Fintype V] [DecidableRel G.Adj] [DecidableEq V] (h : H.Free G) (v : V) :
    #(G.deleteIncidenceSet v).edgeFinset ≤ extremalNumber (card V-1) H := by
  rw [← card_edgeFinset_induce_compl_singleton, ← @card_unique ({v} : Set V), ← card_compl_set]
  apply card_edgeFinset_le_extremalNumber
  contrapose! h
  rw [not_free] at h ⊢
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

lemma extremalNumber_div_choose_two_succ_le {n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph W) :
    (extremalNumber (n+1) H / (n+1).choose 2 : ℝ) ≤ (extremalNumber n H / n.choose 2 : ℝ) := by
  conv_lhs =>
    enter [1, 1, 1]
    rw [← Fintype.card_fin (n+1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n-1 : ℝ), ← mul_div (n-1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc,
    ← mul_div (n+1 : ℝ), mul_comm _ (n/2 : ℝ), mul_assoc, mul_le_mul_left (by positivity),
    ← Nat.cast_pred (by positivity), ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_mul, Nat.cast_le]
  -- double counting `(v, e) ↦ v ∉ e`
  let s := (univ ×ˢ G.edgeFinset).filter fun (v, e) ↦ v ∉ e
  trans #s
  -- counting `e`
  · conv_rhs =>
      rw [card_filter, sum_product_right]
      enter [2, x]
      rw [← card_filter]
    simp_rw [Sym2.mem_toFinset, filter_not, filter_mem_eq_inter, ← sum_attach G.edgeFinset,
      univ_inter, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset,
      sum_const, card_attach, smul_eq_mul, Nat.succ_sub_succ_eq_sub, mul_comm]
    rfl
  -- counting `v`
  · conv_rhs =>
      rw [← Fintype.card_fin (n+1), ← card_univ, ← smul_eq_mul, ← sum_const]
    conv_lhs =>
      rw [card_filter, sum_product]
      enter [2, x]
      rw [← card_filter]
    apply sum_le_sum
    intro i _
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using card_edgeFinset_deleteIncidenceSet_le_extremalNumber h i

/-- The limit `extremalNumber (Fin n) H / n.choose 2` as `n` approaches `∞` exists. -/
lemma exists_tendsto_extremalNumber_div_choose_two (H : SimpleGraph W) :
    ∃ x, Tendsto (fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 x) := by
  let f := fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)
  suffices h : ∃ x, Tendsto (fun (n : ℕ) ↦ f (n + 2)) atTop (𝓝 x) by
    simpa [tendsto_add_atTop_iff_nat 2] using h
  use ⨅ n, f (n + 2)
  apply tendsto_atTop_ciInf
  · apply antitone_nat_of_succ_le
    intro n
    apply extremalNumber_div_choose_two_succ_le
    exact le_add_of_nonneg_left n.zero_le
  · use 0
    intro n ⟨_, hn⟩
    rw [← hn]
    positivity

/-- The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H / n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  have ⟨_, h⟩ := exists_tendsto_extremalNumber_div_choose_two H
  rwa [← Tendsto.limUnder_eq h] at h

/-- `extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
theorem isEquivalent_extremalNumber (h : turanDensity H ≠ 0) :
    (fun (n : ℕ) ↦ (extremalNumber n H : ℝ))
      ~[atTop] (fun (n : ℕ) ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1/turanDensity H : ℝ) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    use 2
    intro n hn
    simp [h, Nat.choose_eq_zero_iff, hn]
  simpa [isEquivalent_iff_tendsto_one hz] using hπ

end SimpleGraph
