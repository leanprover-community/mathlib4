/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.real.enat_ennreal
! leanprover-community/mathlib commit 53b216bcc1146df1c4a0a86877890ea9f1f01589
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Real.Ennreal

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/


open Classical NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

instance hasCoeEnnreal : CoeTC ℕ∞ ℝ≥0∞ :=
  ⟨WithTop.map coe⟩
#align enat.has_coe_ennreal ENat.hasCoeEnnreal

@[simp]
theorem map_coe_nNReal : WithTop.map (coe : ℕ → ℝ≥0) = (coe : ℕ∞ → ℝ≥0∞) :=
  rfl
#align enat.map_coe_nnreal ENat.map_coe_nNReal

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTop_map
#align enat.to_ennreal_order_embedding ENat.toEnnrealOrderEmbedding

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps (config := { fullyApplied := false })]
def toEnnrealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  (Nat.castRingHom ℝ≥0).withTop_map Nat.cast_injective
#align enat.to_ennreal_ring_hom ENat.toEnnrealRingHom

@[simp, norm_cast]
theorem coe_eNNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl
#align enat.coe_ennreal_top ENat.coe_eNNReal_top

@[simp, norm_cast]
theorem coe_eNNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl
#align enat.coe_ennreal_coe ENat.coe_eNNReal_coe

@[simp, norm_cast]
theorem coe_eNNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toEnnrealOrderEmbedding.le_iff_le
#align enat.coe_ennreal_le ENat.coe_eNNReal_le

@[simp, norm_cast]
theorem coe_eNNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toEnnrealOrderEmbedding.lt_iff_lt
#align enat.coe_ennreal_lt ENat.coe_eNNReal_lt

@[mono]
theorem coe_eNNReal_mono : Monotone (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.Monotone
#align enat.coe_ennreal_mono ENat.coe_eNNReal_mono

@[mono]
theorem coe_eNNReal_strictMono : StrictMono (coe : ℕ∞ → ℝ≥0∞) :=
  toEnnrealOrderEmbedding.StrictMono
#align enat.coe_ennreal_strict_mono ENat.coe_eNNReal_strictMono

@[simp, norm_cast]
theorem coe_eNNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toEnnrealRingHom
#align enat.coe_ennreal_zero ENat.coe_eNNReal_zero

@[simp]
theorem coe_eNNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toEnnrealRingHom m n
#align enat.coe_ennreal_add ENat.coe_eNNReal_add

@[simp]
theorem coe_eNNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toEnnrealRingHom
#align enat.coe_ennreal_one ENat.coe_eNNReal_one

@[simp]
theorem coe_eNNReal_bit0 (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) :=
  coe_eNNReal_add n n
#align enat.coe_ennreal_bit0 ENat.coe_eNNReal_bit0

@[simp]
theorem coe_eNNReal_bit1 (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
  map_bit1 toEnnrealRingHom n
#align enat.coe_ennreal_bit1 ENat.coe_eNNReal_bit1

@[simp]
theorem coe_eNNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toEnnrealRingHom m n
#align enat.coe_ennreal_mul ENat.coe_eNNReal_mul

@[simp]
theorem coe_eNNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  coe_eNNReal_mono.map_min
#align enat.coe_ennreal_min ENat.coe_eNNReal_min

@[simp]
theorem coe_eNNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  coe_eNNReal_mono.map_max
#align enat.coe_ennreal_max ENat.coe_eNNReal_max

@[simp]
theorem coe_eNNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n
#align enat.coe_ennreal_sub ENat.coe_eNNReal_sub

end ENat

