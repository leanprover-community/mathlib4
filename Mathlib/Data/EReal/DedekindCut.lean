/-
Copyright (c) 2026 Eric Paul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Paul, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.Completion

/-!
# The Dedekind completion of the rationals

In Mathlib, the real numbers are defined via equivalence classes of Cauchy sequences. A popular
alternative is to instead define them in terms of Dedekind cuts.

This file indirectly formalizes that construction, by proving that the Dedekind completion of the
rationals is order isomorphic to the extended reals.
-/

public noncomputable section

namespace EReal

open DedekindCut Concept Order

@[simp]
theorem upperBounds_setOfPred_ratCast_le (x : EReal) :
    upperBounds {q : ℚ | (q : ℝ) ≤ x} = {q : ℚ | x ≤ (q : ℝ)} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_ratCast_lt_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hz hy

@[simp]
theorem lowerBounds_setOfPred_le_ratCast (x : EReal) :
    lowerBounds {q : ℚ | x ≤ (q : ℝ)} = {q : ℚ | (q : ℝ) ≤ x} := by
  ext y
  constructor
  · refine fun hy ↦ le_of_forall_lt_ratCast_imp_le fun q hq ↦ ?_
    simpa using hy hq.le
  · intro hy z hz
    simpa using le_trans (b := x) hy hz

/-- The Dedekind completion of the rationals is order isomorphic to the extended reals. -/
@[expose] def dedekindCutOrderIso : DedekindCut ℚ ≃o EReal where
  toFun := private factorEmbedding (Rat.castOrderEmbedding.trans Real.coeOrderEmbedding)
  invFun x := {
    extent := {q : ℚ | (q : ℝ) ≤ x}
    intent := {q : ℚ | x ≤ (q : ℝ)}
    upperPolar_extent := by simp
    lowerPolar_intent := by simp
  }
  left_inv x := by
    ext z
    simp only [left_mk, Set.mem_ofPred]
    change _ ≤ factorEmbedding _ x ↔ _
    rw [← principal_le_iff,
      ← (factorEmbedding (Rat.castOrderEmbedding.trans Real.coeOrderEmbedding)).le_iff_le ,
      factorEmbedding_principal]
    rfl
  right_inv x := by
    change factorEmbedding _ _ = x
    rw [factorEmbedding_apply]
    exact le_antisymm (by simp) (le_of_forall_ratCast_lt_imp_le fun q hq ↦ le_sSup ⟨q, hq.le, rfl⟩)
  map_rel_iff' {a b} := by simp

@[simp]
theorem left_dedekindCutOrderIso_symm_apply (x : EReal) :
    (dedekindCutOrderIso.symm x).left = {q : ℚ | (q : ℝ) ≤ x} :=
  rfl

@[simp]
theorem right_dedekindCutOrderIso_symm_apply (x : EReal) :
    (dedekindCutOrderIso.symm x).right = {q : ℚ | x ≤ (q : ℝ)} :=
  rfl

theorem dedekindCutOrderIso_apply_eq_sSup (A : DedekindCut ℚ) :
    dedekindCutOrderIso A = sSup ((fun q : ℚ ↦ ((q : ℝ) : EReal)) '' A.left) :=
  (rfl)

theorem dedekindCutOrderIso_apply_eq_sInf (A : DedekindCut ℚ) :
    dedekindCutOrderIso A = sInf ((fun q : ℚ ↦ ((q : ℝ) : EReal)) '' A.right) := by
  conv_lhs => rw [← A.sInf_image_principal_right]
  rw [OrderIso.map_sInf, ← sInf_image, Set.image_image]
  simp only [dedekindCutOrderIso_principal]

@[simp]
theorem dedekindCutOrderIso_principal (q : ℚ) : dedekindCutOrderIso (principal q) = (q : ℝ) := by
  apply (sSup_le _).antisymm (le_sSup _) <;> simp

end EReal
