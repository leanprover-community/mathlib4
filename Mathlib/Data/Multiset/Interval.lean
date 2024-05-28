/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.DFinsupp.Interval
import Mathlib.Data.DFinsupp.Multiset
import Mathlib.Order.Interval.Finset.Nat

#align_import data.multiset.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of multisets

This file provides the `LocallyFiniteOrder` instance for `Multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `DFinsupp`, rather than via filtering
`Multiset.Powerset`; this is because `(Multiset.replicate n x).Powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `Finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/


open Finset DFinsupp Function

open Pointwise

variable {α : Type*}

namespace Multiset

variable [DecidableEq α] (s t : Multiset α)

instance instLocallyFiniteOrder : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t => (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp

theorem Icc_eq :
    Finset.Icc s t = (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  rfl
#align multiset.Icc_eq Multiset.Icc_eq

theorem uIcc_eq :
    uIcc s t =
      (uIcc (toDFinsupp s) (toDFinsupp t)).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  (Icc_eq _ _).trans <| by simp [uIcc]
#align multiset.uIcc_eq Multiset.uIcc_eq

theorem card_Icc :
    (Finset.Icc s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) := by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
#align multiset.card_Icc Multiset.card_Icc

theorem card_Ico :
    (Finset.Ico s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ico_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ico Multiset.card_Ico

theorem card_Ioc :
    (Finset.Ioc s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ioc Multiset.card_Ioc

theorem card_Ioo :
    (Finset.Ioo s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 2 := by
  rw [Finset.card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align multiset.card_Ioo Multiset.card_Ioo

theorem card_uIcc :
    (uIcc s t).card = ∏ i ∈ s.toFinset ∪ t.toFinset, ((t.count i - s.count i : ℤ).natAbs + 1) := by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
#align multiset.card_uIcc Multiset.card_uIcc

theorem card_Iic : (Finset.Iic s).card = ∏ i ∈ s.toFinset, (s.count i + 1) := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]
#align multiset.card_Iic Multiset.card_Iic

end Multiset
