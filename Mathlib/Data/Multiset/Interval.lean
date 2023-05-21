/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.multiset.interval
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Dfinsupp.Interval
import Mathlib.Data.Dfinsupp.Multiset
import Mathlib.Data.Nat.Interval

/-!
# Finite intervals of multisets

This file provides the `LocallyFiniteOrder` instance for `Multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `Dfinsupp`, rather than via filtering
`Multiset.Powerset`; this is because `(Multiset.replicate n x).Powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `Finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/


open Finset Dfinsupp Function

open BigOperators Pointwise

variable {α : Type _} {β : α → Type _}

namespace Multiset

variable [DecidableEq α] (f g : Multiset α)

instance : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun f g =>
      (Finset.Icc (Multiset.toDfinsupp f) (Multiset.toDfinsupp g)).map
      Multiset.equivDfinsupp.toEquiv.symm.toEmbedding)
    fun f g x => by simp

theorem Icc_eq :
    Finset.Icc f g =
      (Finset.Icc (Multiset.toDfinsupp f) (Multiset.toDfinsupp g)).map
      Multiset.equivDfinsupp.toEquiv.symm.toEmbedding :=
  rfl
#align multiset.Icc_eq Multiset.Icc_eq

theorem card_Icc :
    (Finset.Icc f g).card = ∏ i in f.toFinset ∪ g.toFinset, (g.count i + 1 - f.count i) := by
  simp_rw [Icc_eq, Finset.card_map, Dfinsupp.card_Icc, Nat.card_Icc, Multiset.toDfinsupp_apply,
    toDfinsupp_support]
#align multiset.card_Icc Multiset.card_Icc

theorem card_Ico :
    (Finset.Ico f g).card = ∏ i in f.toFinset ∪ g.toFinset, (g.count i + 1 - f.count i) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ico Multiset.card_Ico

theorem card_Ioc :
    (Finset.Ioc f g).card = ∏ i in f.toFinset ∪ g.toFinset, (g.count i + 1 - f.count i) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ioc Multiset.card_Ioc

theorem card_Ioo :
    (Finset.Ioo f g).card = ∏ i in f.toFinset ∪ g.toFinset, (g.count i + 1 - f.count i) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align multiset.card_Ioo Multiset.card_Ioo

theorem card_Iic : (Finset.Iic f).card = ∏ i in f.toFinset, (f.count i + 1) := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]
#align multiset.card_Iic Multiset.card_Iic

end Multiset
