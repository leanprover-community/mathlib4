/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENNReal.Basic

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/

assert_not_exists Finset

open NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

/-- Coercion from `ℕ∞` to `ℝ≥0∞`. -/
@[coe] def toENNReal : ℕ∞ → ℝ≥0∞ := ENat.map Nat.cast

instance hasCoeENNReal : CoeTC ℕ∞ ℝ≥0∞ := ⟨toENNReal⟩

@[simp]
theorem map_coe_nnreal : ENat.map ((↑) : ℕ → ℝ≥0) = ((↑) : ℕ∞ → ℝ≥0∞) :=
  rfl

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `OrderEmbedding`. -/
@[simps! -fullyApplied]
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTopMap

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps! -fullyApplied]
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  .ENatMap (Nat.castRingHom ℝ≥0) Nat.cast_injective

@[simp, norm_cast]
theorem toENNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl

@[simp, norm_cast]
theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl

@[simp, norm_cast]
theorem toENNReal_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℕ∞) : ℝ≥0∞) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem toENNReal_inj : (m : ℝ≥0∞) = (n : ℝ≥0∞) ↔ m = n :=
  toENNRealOrderEmbedding.eq_iff_eq

@[simp, norm_cast] lemma toENNReal_eq_top : (n : ℝ≥0∞) = ∞ ↔ n = ⊤ := by simp [← toENNReal_inj]
@[norm_cast] lemma toENNReal_ne_top : (n : ℝ≥0∞) ≠ ∞ ↔ n ≠ ⊤ := by simp

@[simp, norm_cast]
theorem toENNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast]
theorem toENNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt

@[simp, norm_cast]
lemma toENNReal_lt_top : (n : ℝ≥0∞) < ∞ ↔ n < ⊤ := by simp [← toENNReal_lt]

@[mono]
theorem toENNReal_mono : Monotone ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.monotone

@[mono]
theorem toENNReal_strictMono : StrictMono ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]
theorem toENNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom

@[simp, norm_cast]
theorem toENNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n

@[simp, norm_cast]
theorem toENNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom

@[simp, norm_cast]
theorem toENNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n

@[simp, norm_cast]
theorem toENNReal_pow (x : ℕ∞) (n : ℕ) : (x ^ n : ℕ∞) = (x : ℝ≥0∞) ^ n :=
  RingHom.map_pow toENNRealRingHom x n

@[simp, norm_cast]
theorem toENNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  toENNReal_mono.map_min

@[simp, norm_cast]
theorem toENNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  toENNReal_mono.map_max

@[simp, norm_cast]
theorem toENNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

end ENat
