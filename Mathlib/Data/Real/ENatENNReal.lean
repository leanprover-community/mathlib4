/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.ENNReal

#align_import data.real.enat_ennreal from "leanprover-community/mathlib"@"53b216bcc1146df1c4a0a86877890ea9f1f01589"

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

@[simp]
theorem map_coe_nnreal : WithTop.map ((↑) : ℕ → ℝ≥0) = ((↑) : ℕ∞ → ℝ≥0∞) :=
  rfl

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `OrderEmbedding`. -/
@[simps! (config := { fullyApplied := false })]
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTopMap

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps! (config := { fullyApplied := false })]
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  .withTopMap (Nat.castRingHom ℝ≥0) Nat.cast_injective

@[simp, norm_cast]
theorem toENNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl

@[simp, norm_cast]
theorem toENNReal_ofNat (n : ℕ) [n.AtLeastTwo] : ((OfNat.ofNat n : ℕ∞) : ℝ≥0∞) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem toENNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast]
theorem toENNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt

@[mono]
theorem toENNReal_mono : Monotone ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.monotone

@[mono]
theorem toENNReal_strictMono : StrictMono ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]
theorem toENNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom

@[simp]
theorem toENNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n

@[simp]
theorem toENNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom

#noalign enat.coe_ennreal_bit0
#noalign enat.coe_ennreal_bit1

@[simp]
theorem toENNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n

@[simp]
theorem toENNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  toENNReal_mono.map_min

@[simp]
theorem toENNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  toENNReal_mono.map_max

@[simp]
theorem toENNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

end ENat
