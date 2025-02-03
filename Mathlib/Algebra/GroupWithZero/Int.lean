/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Lemmas about `ℤₘ₀`.
-/

namespace WithZero

open Multiplicative

theorem ofAdd_zpow (a : ℤ) : (↑(ofAdd a) : ℤₘ₀) = ofAdd (1 : ℤ) ^ a := by
  rw [← WithZero.coe_zpow, WithZero.coe_inj, ← Int.ofAdd_mul, one_mul]

theorem ofAdd_zpow_zpow_comm (a b c : ℤ) :
    ((↑(ofAdd a) : ℤₘ₀) ^ b) ^ c = (ofAdd (a : ℤ) ^ c) ^ b := by
  simp only [← WithZero.coe_zpow]
  rw [← zpow_mul, mul_comm, zpow_mul]

theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  rw [ofAdd_zpow (-1)]
  simp only [zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, ofAdd_zpow_zpow_comm, ← ofAdd_zpow]

end WithZero
