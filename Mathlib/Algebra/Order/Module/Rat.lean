/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Rat.Cast.Order

import Mathlib.Algebra.Module.Rat

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Monotonicity of the action by rational numbers
-/

public section

variable {α : Type*}

instance PosSMulMono.nnrat_of_rat [Preorder α] [MulAction ℚ α] [MulAction ℚ≥0 α]
    [IsScalarTower ℚ≥0 ℚ α] [PosSMulMono ℚ α] :
    PosSMulMono ℚ≥0 α where
  smul_le_smul_of_nonneg_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul ℚ, ← NNRat.cast_smul_eq_nnqsmul ℚ]
    exact smul_le_smul_of_nonneg_left (α := ℚ) ha hq

instance PosSMulStrictMono.nnrat_of_rat [Preorder α] [MulAction ℚ≥0 α] [MulAction ℚ α]
    [IsScalarTower ℚ≥0 ℚ α] [PosSMulStrictMono ℚ α] :
    PosSMulStrictMono ℚ≥0 α where
  smul_lt_smul_of_pos_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul ℚ, ← NNRat.cast_smul_eq_nnqsmul ℚ]
    exact smul_lt_smul_of_pos_left (α := ℚ) ha hq

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

@[simp] lemma abs_nnqsmul [DistribMulAction ℚ≥0 α] [PosSMulMono ℚ≥0 α] (q : ℚ≥0) (a : α) :
    |q • a| = q • |a| := by
  obtain ha | ha := le_total a 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos]

end LinearOrderedAddCommGroup

section LinearOrderedSemifield
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

instance LinearOrderedSemifield.toPosSMulStrictMono_rat : PosSMulStrictMono ℚ≥0 α where
  smul_lt_smul_of_pos_left q hq a b hab := by
    rw [NNRat.smul_def, NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab <| NNRat.cast_pos.2 hq

instance LinearOrderedSemifield.toPosSMulMono_nnrat : PosSMulMono ℚ≥0 α where
  smul_le_smul_of_nonneg_left q _ a b hab := by
    rw [NNRat.smul_def, NNRat.smul_def]; exact mul_le_mul_of_nonneg_left hab q.cast_nonneg

instance LinearOrderedSemifield.toSMulPosMono_nnrat : SMulPosMono ℚ≥0 α where
  smul_le_smul_of_nonneg_right a ha q r hqr := by
    rw [NNRat.smul_def, NNRat.smul_def]
    exact mul_le_mul_of_nonneg_right (NNRat.cast_le.2 hqr) ha

instance LinearOrderedSemifield.toSMulPosStrictMono_nnrat : SMulPosStrictMono ℚ≥0 α where
  smul_lt_smul_of_pos_right a ha q r hqr := by
    rw [NNRat.smul_def, NNRat.smul_def]
    exact mul_lt_mul_of_pos_right (NNRat.cast_lt.2 hqr) ha

instance LinearOrderedSemifield.toPosSMulReflectLT_nnrat : PosSMulReflectLT ℚ≥0 α where
  lt_of_smul_lt_smul_left q _ a b h := by
    rw [NNRat.smul_def, NNRat.smul_def] at h; exact lt_of_mul_lt_mul_left h q.cast_nonneg

instance LinearOrderedSemifield.toSMulPosReflectLE_nnrat : SMulPosReflectLE ℚ≥0 α where
  le_of_smul_le_smul_right a ha q r h := by
    rw [NNRat.smul_def, NNRat.smul_def] at h; exact NNRat.cast_le.1 (le_of_mul_le_mul_right h ha)

instance LinearOrderedSemifield.toSMulPosReflectLT_nnrat : SMulPosReflectLT ℚ≥0 α where
  lt_of_smul_lt_smul_right a ha q r h := by
    rw [NNRat.smul_def, NNRat.smul_def] at h; exact NNRat.cast_lt.1 (lt_of_mul_lt_mul_right h ha)

end LinearOrderedSemifield

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

instance LinearOrderedField.toPosSMulStrictMono_rat : PosSMulStrictMono ℚ α where
  smul_lt_smul_of_pos_left q hq a b hab := by
    rw [Rat.smul_def, Rat.smul_def]; exact mul_lt_mul_of_pos_left hab <| Rat.cast_pos.2 hq

instance LinearOrderedField.toPosSMulMono_rat : PosSMulMono ℚ α where
  smul_le_smul_of_nonneg_left q hq a b hab := by
    rw [Rat.smul_def, Rat.smul_def]; exact mul_le_mul_of_nonneg_left hab <| Rat.cast_nonneg.2 hq

instance LinearOrderedField.toSMulPosMono_rat : SMulPosMono ℚ α where
  smul_le_smul_of_nonneg_right a ha q r hqr := by
    rw [Rat.smul_def, Rat.smul_def]; exact mul_le_mul_of_nonneg_right (Rat.cast_le.2 hqr) ha

instance LinearOrderedField.toSMulPosStrictMono_rat : SMulPosStrictMono ℚ α where
  smul_lt_smul_of_pos_right a ha q r hqr := by
    rw [Rat.smul_def, Rat.smul_def]; exact mul_lt_mul_of_pos_right (Rat.cast_lt.2 hqr) ha

instance LinearOrderedField.toPosSMulReflectLT_rat : PosSMulReflectLT ℚ α where
  lt_of_smul_lt_smul_left q hq a b h := by
    rw [Rat.smul_def, Rat.smul_def] at h; exact lt_of_mul_lt_mul_left h <| Rat.cast_nonneg.2 hq

instance LinearOrderedField.toSMulPosReflectLE_rat : SMulPosReflectLE ℚ α where
  le_of_smul_le_smul_right a ha q r h := by
    rw [Rat.smul_def, Rat.smul_def] at h; exact Rat.cast_le.1 (le_of_mul_le_mul_right h ha)

instance LinearOrderedField.toSMulPosReflectLT_rat : SMulPosReflectLT ℚ α where
  lt_of_smul_lt_smul_right a ha q r h := by
    rw [Rat.smul_def, Rat.smul_def] at h; exact Rat.cast_lt.1 (lt_of_mul_lt_mul_right h ha)

end LinearOrderedField
