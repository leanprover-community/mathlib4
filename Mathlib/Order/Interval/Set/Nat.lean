/-
Copyright (c) 2026 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
module

public import Mathlib.Data.Set.Card

import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite intervals of naturals

This file calculates the cardinality of intervals of natural numbers as sets.
-/

public section

namespace Set

@[simp] lemma ncard_Icc_nat (a b : ℕ) : (Icc a b).ncard = b + 1 - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Icc a b

@[simp] lemma ncard_Ico_nat (a b : ℕ) : (Ico a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ico a b

@[simp] lemma ncard_Ioc_nat (a b : ℕ) : (Ioc a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioc a b

@[simp] lemma ncard_Ioo_nat (a b : ℕ) : (Ioo a b).ncard = b - a - 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioo a b

@[simp] lemma ncard_uIcc_nat (a b : ℕ) : (uIcc a b).ncard = (b - a : ℤ).natAbs + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_uIcc a b

@[simp] lemma ncard_Iic_nat (b : ℕ) : (Iic b).ncard = b + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iic b

@[simp] lemma ncard_Iio_nat (b : ℕ) : (Iio b).ncard = b := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iio b

end Set
