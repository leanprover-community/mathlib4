/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.DFinsupp.Order

#align_import data.dfinsupp.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/


open DFinsupp Finset

open BigOperators Pointwise

variable {ι : Type*} {α : ι → Type*}

namespace Finset

variable [DecidableEq ι] [∀ i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : ∀ i, Finset (α i)}

/-- Finitely supported product of finsets. -/
def dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine' (mk_injective _).comp fun f g h => _
      -- ⊢ f = g
      ext i hi
      -- ⊢ f i hi = g i hi
      convert congr_fun h ⟨i, hi⟩⟩
      -- 🎉 no goals
#align finset.dfinsupp Finset.dfinsupp

@[simp]
theorem card_dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) :
    (s.dfinsupp t).card = ∏ i in s, (t i).card :=
  (card_map _).trans <| card_pi _ _
#align finset.card_dfinsupp Finset.card_dfinsupp

variable [∀ i, DecidableEq (α i)]

theorem mem_dfinsupp_iff : f ∈ s.dfinsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  refine' mem_map.trans ⟨_, _⟩
  -- ⊢ (∃ a, a ∈ pi s t ∧ ↑{ toFun := fun f => DFinsupp.mk s fun i => f ↑i (_ : ↑i  …
  · rintro ⟨f, hf, rfl⟩
    -- ⊢ support (↑{ toFun := fun f => DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s), inj …
    rw [Function.Embedding.coeFn_mk] -- porting note: added to avoid heartbeat timeout
    -- ⊢ support (DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s)) ⊆ s ∧ ∀ (i : ι), i ∈ s → …
    refine' ⟨support_mk_subset, fun i hi => _⟩
    -- ⊢ ↑(DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s)) i ∈ t i
    convert mem_pi.1 hf i hi
    -- ⊢ ↑(DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s)) i = f i hi
    exact mk_of_mem hi
    -- 🎉 no goals
  · refine' fun h => ⟨fun i _ => f i, mem_pi.2 h.2, _⟩
    -- ⊢ (↑{ toFun := fun f => DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s), inj' := (_  …
    ext i
    -- ⊢ ↑(↑{ toFun := fun f => DFinsupp.mk s fun i => f ↑i (_ : ↑i ∈ ↑s), inj' := (_ …
    dsimp
    -- ⊢ (if i ∈ s then ↑f i else 0) = ↑f i
    exact ite_eq_left_iff.2 fun hi => (not_mem_support_iff.1 fun H => hi <| h.1 H).symm
    -- 🎉 no goals
#align finset.mem_dfinsupp_iff Finset.mem_dfinsupp_iff

/-- When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is pointwise in `t`.
-/
@[simp]
theorem mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.support ⊆ s) :
    f ∈ s.dfinsupp t ↔ ∀ i, f i ∈ t i := by
  refine' mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => _,
        fun h => ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi _, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    -- ⊢ ↑f i ∈ ↑t i
    · exact h.2 hi
      -- 🎉 no goals
    · rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (not_mem_mono ht hi)]
      -- ⊢ 0 ∈ 0
      exact zero_mem_zero
      -- 🎉 no goals
  · rwa [H, mem_zero] at h
    -- 🎉 no goals
#align finset.mem_dfinsupp_iff_of_support_subset Finset.mem_dfinsupp_iff_of_support_subset

end Finset

open Finset

namespace DFinsupp

section BundledSingleton

variable [∀ i, Zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `Finset.singleton` bundled as a `DFinsupp`. -/
def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩
#align dfinsupp.singleton DFinsupp.singleton

theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton
#align dfinsupp.mem_singleton_apply_iff DFinsupp.mem_singleton_apply_iff

end BundledSingleton

section BundledIcc

variable [∀ i, Zero (α i)] [∀ i, PartialOrder (α i)] [∀ i, LocallyFiniteOrder (α i)]
  {f g : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `Finset.Icc` bundled as a `DFinsupp`. -/
def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.not_mem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        have hg : g i = 0 := (gs.prop i).resolve_left
            (Multiset.not_mem_mono (Multiset.Le.subset <| Multiset.le_add_left _ _) h)
        -- porting note: was rw, but was rewriting under lambda, so changed to simp_rw
        simp_rw [hf, hg]
        -- ⊢ Icc 0 0 = 0
        exact Icc_self _⟩
        -- 🎉 no goals
#align dfinsupp.range_Icc DFinsupp.rangeIcc

@[simp]
theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl
#align dfinsupp.range_Icc_apply DFinsupp.rangeIcc_apply

theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc
#align dfinsupp.mem_range_Icc_apply_iff DFinsupp.mem_rangeIcc_apply_iff

theorem support_rangeIcc_subset [DecidableEq ι] [∀ i, DecidableEq (α i)] :
    (f.rangeIcc g).support ⊆ f.support ∪ g.support := by
  refine' fun x hx => _
  -- ⊢ x ∈ support f ∪ support g
  by_contra h
  -- ⊢ False
  refine' not_mem_support_iff.2 _ hx
  -- ⊢ ↑(rangeIcc f g) x = 0
  rw [rangeIcc_apply, not_mem_support_iff.1 (not_mem_mono (subset_union_left _ _) h),
    not_mem_support_iff.1 (not_mem_mono (subset_union_right _ _) h)]
  exact Icc_self _
  -- 🎉 no goals
#align dfinsupp.support_range_Icc_subset DFinsupp.support_rangeIcc_subset

end BundledIcc

section Pi

variable [∀ i, Zero (α i)] [DecidableEq ι] [∀ i, DecidableEq (α i)]

/-- Given a finitely supported function `f : Π₀ i, Finset (α i)`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) := f.support.dfinsupp f
#align dfinsupp.pi DFinsupp.pi

@[simp]
theorem mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_dfinsupp_iff_of_support_subset <| Subset.refl _
#align dfinsupp.mem_pi DFinsupp.mem_pi

@[simp]
theorem card_pi (f : Π₀ i, Finset (α i)) : f.pi.card = f.prod fun i => (f i).card := by
  rw [pi, card_dfinsupp]
  -- ⊢ ∏ i in support f, card (↑f i) = prod f fun i => ↑(card (↑f i))
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.nat_apply, Nat.cast_id]
  -- 🎉 no goals
#align dfinsupp.card_pi DFinsupp.card_pi

end Pi

section PartialOrder

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

variable [∀ i, PartialOrder (α i)] [∀ i, Zero (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (Π₀ i, α i) :=
  LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support ∪ g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine' (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans _
      -- ⊢ (∀ (i : ι), ↑x i ∈ ↑(rangeIcc f g) i) ↔ f ≤ x ∧ x ≤ g
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      -- ⊢ ((∀ (x_1 : ι), ↑f x_1 ≤ ↑x x_1) ∧ ∀ (x_1 : ι), ↑x x_1 ≤ ↑g x_1) ↔ f ≤ x ∧ x  …
      rfl)
      -- 🎉 no goals

variable (f g : Π₀ i, α i)

theorem Icc_eq : Icc f g = (f.support ∪ g.support).dfinsupp (f.rangeIcc g) := rfl
#align dfinsupp.Icc_eq DFinsupp.Icc_eq

theorem card_Icc : (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card :=
  card_dfinsupp _ _
#align dfinsupp.card_Icc DFinsupp.card_Icc

theorem card_Ico : (Ico f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
  -- 🎉 no goals
#align dfinsupp.card_Ico DFinsupp.card_Ico

theorem card_Ioc : (Ioc f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
  -- 🎉 no goals
#align dfinsupp.card_Ioc DFinsupp.card_Ioc

theorem card_Ioo : (Ioo f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
  -- 🎉 no goals
#align dfinsupp.card_Ioo DFinsupp.card_Ioo

end PartialOrder

section Lattice
variable [DecidableEq ι] [∀ i, DecidableEq (α i)] [∀ i, Lattice (α i)] [∀ i, Zero (α i)]
  [∀ i, LocallyFiniteOrder (α i)] (f g : Π₀ i, α i)

theorem card_uIcc : (uIcc f g).card = ∏ i in f.support ∪ g.support, (uIcc (f i) (g i)).card := by
  rw [←support_inf_union_support_sup]; exact card_Icc _ _
  -- ⊢ card (uIcc f g) = ∏ i in support (f ⊓ g) ∪ support (f ⊔ g), card (uIcc (↑f i …
                                       -- 🎉 no goals
#align dfinsupp.card_uIcc DFinsupp.card_uIcc

end Lattice

section CanonicallyOrdered

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

variable [∀ i, CanonicallyOrderedAddMonoid (α i)] [∀ i, LocallyFiniteOrder (α i)]

variable (f : Π₀ i, α i)

theorem card_Iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card := by
  simp_rw [Iic_eq_Icc, card_Icc, DFinsupp.bot_eq_zero, support_zero, empty_union, zero_apply,
    bot_eq_zero]
#align dfinsupp.card_Iic DFinsupp.card_Iic

theorem card_Iio : (Iio f).card = (∏ i in f.support, (Iic (f i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
  -- 🎉 no goals
#align dfinsupp.card_Iio DFinsupp.card_Iio

end CanonicallyOrdered

end DFinsupp
