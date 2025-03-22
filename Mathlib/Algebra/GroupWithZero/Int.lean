/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Lemmas about `ℤₘ₀`.
-/

local notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

namespace WithZero

open Int Multiplicative

theorem ofAdd_zpow (a : ℤ) : (↑(ofAdd a) : ℤₘ₀) = ofAdd (1 : ℤ) ^ a := by
  rw [← coe_zpow, coe_inj, ← ofAdd_mul, one_mul]

theorem ofAdd_neg_one_pow_comm (a : ℤ) (n : ℕ) :
    ((↑(ofAdd (-1 : ℤ)) : ℤₘ₀) ^ (-a)) ^ n = ofAdd (n : ℤ) ^ a := by
  simp only [ofAdd_zpow (-1), zpow_neg, zpow_one, inv_zpow', inv_inv, coe_zpow]
  rw [← zpow_natCast, zpow_comm, ← ofAdd_zpow]

end WithZero
