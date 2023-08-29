/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Finsupp.Order

#align_import data.finsupp.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `Finsupp.rangeSingleton`: Postcomposition with `Singleton.singleton` on `Finset` as a
  `Finsupp`.
* `Finsupp.rangeIcc`: Postcomposition with `Finset.Icc` as a `Finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/

noncomputable section

open Finset Finsupp Function

open BigOperators Classical Pointwise

variable {ι α : Type*}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `Singleton.singleton` bundled as a `Finsupp`. -/
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    -- ⊢ ↑f i = 0 ↔ (fun i => {↑f i}) i = 0
    exact singleton_injective.eq_iff.symm
    -- 🎉 no goals
#align finsupp.range_singleton Finsupp.rangeSingleton

theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton
#align finsupp.mem_range_singleton_apply_iff Finsupp.mem_rangeSingleton_apply_iff

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `Finset.Icc` bundled as a `Finsupp`. -/
@[simps toFun]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α where
  toFun i := Icc (f i) (g i)
  support :=
    -- porting note: Not needed (due to open Classical), in mathlib3 too
    -- haveI := Classical.decEq ι
    f.support ∪ g.support
  mem_support_toFun i := by
    rw [mem_union, ← not_iff_not, not_or, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    -- ⊢ ↑f i = 0 ∧ ↑g i = 0 ↔ (fun i => Icc (↑f i) (↑g i)) i = 0
    exact Icc_eq_singleton_iff.symm
    -- 🎉 no goals
#align finsupp.range_Icc Finsupp.rangeIcc

-- porting note: Added as alternative to rangeIcc_toFun to be used in proof of card_Icc
lemma coe_rangeIcc (f g : ι →₀ α) : rangeIcc f g i = Icc (f i) (g i) := rfl

@[simp]
theorem rangeIcc_support (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := rfl
#align finsupp.range_Icc_support Finsupp.rangeIcc_support

theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc
#align finsupp.mem_range_Icc_apply_iff Finsupp.mem_rangeIcc_apply_iff

end RangeIcc

section PartialOrder

variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

instance : LocallyFiniteOrder (ι →₀ α) :=
  -- porting note: Not needed (due to open Classical), in mathlib3 too
  -- haveI := Classical.decEq ι
  -- haveI := Classical.decEq α
  LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.support ∪ g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine'
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans _
      simp_rw [mem_rangeIcc_apply_iff]
      -- ⊢ (∀ (i : ι), ↑f i ≤ ↑x i ∧ ↑x i ≤ ↑g i) ↔ f ≤ x ∧ x ≤ g
      exact forall_and
      -- 🎉 no goals

theorem Icc_eq : Icc f g = (f.support ∪ g.support).finsupp (f.rangeIcc g) := rfl
#align finsupp.Icc_eq Finsupp.Icc_eq

-- porting note: removed [DecidableEq ι]
theorem card_Icc : (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card := by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]
  -- 🎉 no goals
#align finsupp.card_Icc Finsupp.card_Icc

-- porting note: removed [DecidableEq ι]
theorem card_Ico : (Ico f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
  -- 🎉 no goals
#align finsupp.card_Ico Finsupp.card_Ico

-- porting note: removed [DecidableEq ι]
theorem card_Ioc : (Ioc f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
  -- 🎉 no goals
#align finsupp.card_Ioc Finsupp.card_Ioc

-- porting note: removed [DecidableEq ι]
theorem card_Ioo : (Ioo f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
  -- 🎉 no goals
#align finsupp.card_Ioo Finsupp.card_Ioo

end PartialOrder

section Lattice
variable [Lattice α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

-- porting note: removed [DecidableEq ι]
theorem card_uIcc :
    (uIcc f g).card = ∏ i in f.support ∪ g.support, (uIcc (f i) (g i)).card := by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι →₀ α) _
  -- ⊢ card (uIcc f g) = ∏ i in (f ⊓ g).support ∪ (f ⊔ g).support, card (uIcc (↑f i …
                                        -- 🎉 no goals
#align finsupp.card_uIcc Finsupp.card_uIcc

end Lattice

section CanonicallyOrdered

variable [CanonicallyOrderedAddMonoid α] [LocallyFiniteOrder α]

variable (f : ι →₀ α)

theorem card_Iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card := by
  classical simp_rw [Iic_eq_Icc, card_Icc, Finsupp.bot_eq_zero, support_zero, empty_union,
      zero_apply, bot_eq_zero]
#align finsupp.card_Iic Finsupp.card_Iic

theorem card_Iio : (Iio f).card = (∏ i in f.support, (Iic (f i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
  -- 🎉 no goals
#align finsupp.card_Iio Finsupp.card_Iio

end CanonicallyOrdered

end Finsupp
