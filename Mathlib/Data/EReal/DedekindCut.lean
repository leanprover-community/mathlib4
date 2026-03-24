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

/-- The order embedding from the completion of `ℚ` to `EReal` -/
noncomputable def factorEmbeddingRat : DedekindCut ℚ ↪o EReal :=
  factorEmbedding (Rat.castOrderEmbedding.trans Real.coeOrderEmbedding)

theorem factorEmbeddingRat_apply (x : DedekindCut ℚ) :
  factorEmbeddingRat x = sSup ((fun (a : ℚ) ↦ ((a : ℝ) : EReal)) '' x.extent) := rfl

theorem le_of_forall_lt_rat_imp_le {x y : EReal}
    (h : ∀ q : ℚ, y < (q : ℝ) → x ≤ (q : ℝ)) : x ≤ y := by
  by_contra!
  obtain ⟨r, y_lt_r, r_lt_x⟩ := exists_rat_btwn_of_lt this
  order [h r y_lt_r]

theorem le_of_forall_rat_lt_imp_le {x y : EReal}
    (h : ∀ q : ℚ, (q : ℝ) < x → (q : ℝ) ≤ y) : x ≤ y := by
  by_contra!
  obtain ⟨r, y_lt_r, r_lt_x⟩ := exists_rat_btwn_of_lt this
  order [h r r_lt_x]

theorem upperBounds_ratLowerBounds (x : EReal) :
    upperBounds {q : ℚ | (q : ℝ) ≤ x} = {q : ℚ | x ≤ (q : ℝ)} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_rat_lt_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hz hy

theorem lowerBounds_ratUpperBounds (x : EReal) :
    lowerBounds {q : ℚ | x ≤ (q : ℝ)} = {q : ℚ | (q : ℝ) ≤ x} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_lt_rat_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hy hz

def isExtent_ratLowerBounds (x : EReal) : IsExtent (· ≤ ·) {q : ℚ | (q : ℝ) ≤ x} := by
  simp only [isExtent_iff, upperPolar_le, lowerPolar_le, upperBounds_ratLowerBounds,
    lowerBounds_ratUpperBounds]

theorem extent_eRealEmbedDedekindCut_apply (x : EReal) :
  (ofIsExtent (· ≤ ·) {q : ℚ | (q : ℝ) ≤ x} (isExtent_ratLowerBounds x)).extent =
  {q : ℚ | (q : ℝ) ≤ x} := rfl

public noncomputable def completeRat_iso_EReal : DedekindCut ℚ ≃o EReal where
  toFun := factorEmbeddingRat
  invFun x := ofIsExtent (· ≤ ·) {q : ℚ | (q : ℝ) ≤ x} (isExtent_ratLowerBounds x)
  left_inv := by
    intro x
    ext z
    simp only [factorEmbeddingRat_apply, extent_eRealEmbedDedekindCut_apply, Set.mem_setOf_eq,
      sSup_image]
    constructor
    · intro z_le_sup
      simp_rw [← x.lowerBounds_right, ← x.upperBounds_left, mem_lowerBounds, mem_upperBounds]
      intro r hr
      simp only [le_iSup_iff, iSup_le_iff] at z_le_sup
      exact_mod_cast (z_le_sup ((r : ℝ) : EReal) (fun t ht => by exact_mod_cast hr t ht))
    · exact fun z_mem_extent ↦ le_iSup₂_of_le z z_mem_extent le_rfl
  right_inv := by
    intro x
    simp only [factorEmbeddingRat_apply, extent_eRealEmbedDedekindCut_apply]
    apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
    · simp
    · simp only [Set.mem_image, exists_exists_and_eq_and]
      intro w w_lt_x
      obtain ⟨r, w_lt_r, r_lt_x⟩ := exists_rat_btwn_of_lt w_lt_x
      exact ⟨r, r_lt_x.le, w_lt_r⟩
  map_rel_iff' := by simp

end EReal
