/-
Copyright (c) 2026 Eric Paul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Paul
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.Completion

import Mathlib.Tactic.Order

/-!
# The Dedekind completion of the rationals

This file proves that the Dedekind completion of the rationals
is order isomorphic to the extended reals.
-/

namespace EReal

open DedekindCut Concept Order

theorem ratEmbedEReal_apply (x : ℚ) :
  Rat.castOrderEmbedding.trans Real.coeOrderEmbedding x = ((x : ℝ) : EReal) := rfl

@[simp]
theorem upperBounds_setOf_ratCast_le (x : EReal) :
    upperBounds {q : ℚ | (q : ℝ) ≤ x} = {q : ℚ | x ≤ (q : ℝ)} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_rat_lt_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hz hy

@[simp]
theorem lowerBounds_setOf_le_ratCast (x : EReal) :
    lowerBounds {q : ℚ | x ≤ (q : ℝ)} = {q : ℚ | (q : ℝ) ≤ x} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_lt_rat_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hy hz

/-- The Dedekind completion of the rationals is order isomorphic to the extended reals. -/
public noncomputable def dedekindCutOrderIso : DedekindCut ℚ ≃o EReal where
  toFun := factorEmbedding (Rat.castOrderEmbedding.trans Real.coeOrderEmbedding)
  invFun x := {
    extent := {q : ℚ | (q : ℝ) ≤ x}
    intent := {q : ℚ | x ≤ (q : ℝ)}
    upperPolar_extent := by simp
    lowerPolar_intent := by simp
  }
  left_inv := by
    intro x
    ext z
    simp only [factorEmbedding_apply, ratEmbedEReal_apply, sSup_image, iSup_le_iff, extent_mk,
      Set.mem_setOf_eq]
    constructor
    · intro z_le_sup
      simp_rw [← x.lowerBounds_right, ← x.upperBounds_left, mem_lowerBounds, mem_upperBounds]
      intro r hr
      simp only [le_iSup_iff, iSup_le_iff] at z_le_sup
      exact_mod_cast (z_le_sup ((r : ℝ) : EReal) (fun t ht => by simp [hr t ht]))
    · exact fun z_mem_extent ↦ le_iSup₂_of_le z z_mem_extent le_rfl
  right_inv := by
    intro x
    simp only [factorEmbedding_apply, ratEmbedEReal_apply]
    apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
    · simp
    · simp only [Set.mem_image, exists_exists_and_eq_and]
      intro w w_lt_x
      obtain ⟨r, w_lt_r, r_lt_x⟩ := exists_rat_btwn_of_lt w_lt_x
      exact ⟨r, r_lt_x.le, w_lt_r⟩
  map_rel_iff' := by simp

@[simp]
theorem left_dedekindCutOrderIso_symm_apply (x : EReal) :
  (dedekindCutOrderIso.symm x).left = {q : ℚ | (q : ℝ) ≤ x} := rfl

@[simp]
theorem right_dedekindCutOrderIso_symm_apply (x : EReal) :
  (dedekindCutOrderIso.symm x).right = {q : ℚ | x ≤ (q : ℝ)} := rfl

theorem dedekindCutOrderIso_apply_eq_sSup (A : DedekindCut ℚ) :
  dedekindCutOrderIso A = sSup ((fun q : ℚ ↦ ((q : ℝ) : EReal)) '' A.left) := rfl

theorem dedekindCutOrderIso_apply_eq_sInf (A : DedekindCut ℚ) :
    dedekindCutOrderIso A = sInf ((fun q : ℚ ↦ ((q : ℝ) : EReal)) '' A.right) := by
  simp only [dedekindCutOrderIso_apply_eq_sSup, sSup_image, sInf_image]
  apply le_antisymm
  · simp only [← upperBounds_left, le_iInf_iff, iSup_le_iff, EReal.coe_le_coe_iff, Rat.cast_le]
    intro _ mem_right _ mem_left
    exact mem_right mem_left
  · by_contra
    simp only [not_le, lt_iInf_iff, le_iInf_iff] at this
    obtain ⟨b, sup_lt_b, b_le_right⟩ := this
    simp only [iSup_lt_iff, iSup_le_iff] at sup_lt_b
    obtain ⟨c, c_lt_b, left_lt_c⟩ := sup_lt_b
    obtain ⟨q, sup_lt_q, q_lt_b⟩ := exists_rat_btwn_of_lt c_lt_b
    have : ∀ t ∈ A.left, t < q := by
      intro t t_mem_left
      have : ((t : ℝ) : EReal) < (q : ℝ) := by order [left_lt_c t t_mem_left]
      simpa
    have q_mem_right : q ∈ A.right := by
      simp only [← upperBounds_left]
      intro t t_mem_left
      order [this t t_mem_left]
    order [b_le_right q q_mem_right]

end EReal
