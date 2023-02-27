/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.real.enat_ennreal
! leanprover-community/mathlib commit 53b216bcc1146df1c4a0a86877890ea9f1f01589
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.ENNReal

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/


open Classical NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

/-- Coercion from `ℕ∞` to `ℝ≥0∞`. -/
@[coe] def toENNReal : ℕ∞ → ℝ≥0∞ := WithTop.map Nat.cast

instance hasCoeENNReal : CoeTC ℕ∞ ℝ≥0∞ := ⟨toENNReal⟩
#align enat.has_coe_ennreal ENat.hasCoeENNReal

@[simp]
theorem map_coe_nnreal : WithTop.map ((↑) : ℕ → ℝ≥0) = ((↑) : ℕ∞ → ℝ≥0∞) :=
  rfl
#align enat.map_coe_nnreal ENat.map_coe_nnreal

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps! (config := { fullyApplied := false })]
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTopMap
#align enat.to_ennreal_order_embedding ENat.toENNRealOrderEmbedding

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps! (config := { fullyApplied := false })]
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  .withTopMap (Nat.castRingHom ℝ≥0) Nat.cast_injective
#align enat.to_ennreal_ring_hom ENat.toENNRealRingHom

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl
#align enat.coe_ennreal_top ENat.coe_ennreal_top

@[simp, norm_cast]
theorem coe_ennreal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl
#align enat.coe_ennreal_coe ENat.coe_ennreal_coe

@[simp, norm_cast]
theorem coe_ennreal_ofNat (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : ℕ∞) : ℝ≥0∞) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le
#align enat.coe_ennreal_le ENat.coe_ennreal_le

@[simp, norm_cast]
theorem coe_ennreal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt
#align enat.coe_ennreal_lt ENat.coe_ennreal_lt

@[mono]
theorem coe_ennreal_mono : Monotone ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.monotone
#align enat.coe_ennreal_mono ENat.coe_ennreal_mono

@[mono]
theorem coe_ennreal_strictMono : StrictMono ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.strictMono
#align enat.coe_ennreal_strict_mono ENat.coe_ennreal_strictMono

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom
#align enat.coe_ennreal_zero ENat.coe_ennreal_zero

@[simp]
theorem coe_ennreal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n
#align enat.coe_ennreal_add ENat.coe_ennreal_add

@[simp]
theorem coe_ennreal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom
#align enat.coe_ennreal_one ENat.coe_ennreal_one

#noalign enat.coe_ennreal_bit0
#noalign enat.coe_ennreal_bit1

@[simp]
theorem coe_ennreal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n
#align enat.coe_ennreal_mul ENat.coe_ennreal_mul

@[simp]
theorem coe_ennreal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_min
#align enat.coe_ennreal_min ENat.coe_ennreal_min

@[simp]
theorem coe_ennreal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  coe_ennreal_mono.map_max
#align enat.coe_ennreal_max ENat.coe_ennreal_max

@[simp]
theorem coe_ennreal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n
#align enat.coe_ennreal_sub ENat.coe_ennreal_sub

end ENat

