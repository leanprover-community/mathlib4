/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Asymptotics.Defs
import Batteries.Tactic.Trans
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset`: simple graphs on `n` vertices with at least
  `(turanDensity H + o(1)) * n ^ 2` edges contain `H`, for all sufficiently large `n`.
-/

@[expose] public section


open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {W : Type*}

lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n - 1 : ℝ), ← mul_div (n - 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_comm (n - 1 : ℝ), ← mul_div (n + 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_le_mul_iff_right₀ (by positivity), ← Nat.cast_pred (by positivity), ← Nat.cast_mul,
    ← Nat.cast_add_one, ← Nat.cast_mul, Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n + 1), ← card_univ]
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
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ ↦ ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  rwa [← h_tto.limUnder_eq] at h_tto

theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

/-- The **Turán density** of a simple graph `H` is well-defined. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

/-- `extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
theorem isEquivalent_extremalNumber {H : SimpleGraph W} (h : turanDensity H ≠ 0) :
    (fun n ↦ (extremalNumber n H : ℝ)) ~[atTop] (fun n ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / turanDensity H : ℝ) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn ↦ ?_⟩
    simpa [h, Nat.choose_eq_zero_iff]
  simpa [isEquivalent_iff_tendsto_one hz] using hπ

/-- Simple graphs on `n` vertices having at least `(turanDensity H + o(1)) * n ^ 2` edges contain
`H`, for sufficiently large `n`. -/
theorem eventually_isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G := by
  have hπ := (turanDensity_eq_csInf H).ge
  rw [eventually_atTop]
  contrapose! hπ with h
  apply lt_of_lt_of_le <| lt_add_of_pos_right (turanDensity H) hε_pos
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ ↦ ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  rw [← hx]
  have ⟨n, hn, G, _, hcard_edges, h_free⟩ := h m
  replace h_free : H.Free G := not_nonempty_iff.mpr h_free
  trans (extremalNumber n H / n.choose 2)
  · rw [le_div_iff₀ <| mod_cast Nat.choose_pos (hm.trans hn)]
    conv =>
      enter [2, 1, 1]
      rw [← Fintype.card_fin n]
    exact hcard_edges.trans (mod_cast card_edgeFinset_le_extremalNumber h_free)
  · exact antitoneOn_extremalNumber_div_choose_two H hm (hm.trans hn) hn

open Classical in
/-- The edge density of `H`-free simple graphs on `turanDensityConst H ε` vertices
is at most `turanDensity H + ε`.

Contrapositively, `turanDensity H + ε` is the density at which `H` is always contained in simple
graphs on `turanDensityConst H ε` vertices.

Note that this value is only defined for positive `ε` and `turanDensityConst H ε = 0` for non
positive `ε`. -/
noncomputable abbrev turanDensityConst (H : SimpleGraph W) (ε : ℝ) :=
  if h : ε > 0 then
    Nat.find <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H h
  else 0

open Classical in
/-- Simple graphs on `card V` vertices having at least `(turanDensity H + o(1)) * (card V) ^ 2`
edges contain `H`, for sufficiently large `card V`. -/
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    {V : Type*} [Fintype V] (h_verts : card V ≥ turanDensityConst H ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≥ (turanDensity H + ε) * (card V).choose 2 → H ⊑ G := by
  rw [(G.overFinIso rfl).card_edgeFinset_eq, isContained_congr Iso.refl (G.overFinIso rfl)]
  apply Nat.find_spec <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

end SimpleGraph
