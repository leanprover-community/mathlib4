/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.int.interval
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Lemmas
import Mathbin.Order.LocallyFinite
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Int

instance : LocallyFiniteOrder ℤ
    where
  finsetIcc a b :=
    (Finset.range (b + 1 - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIco a b := (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIoc a b :=
    (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finsetIoo a b :=
    (Finset.range (b - a - 1).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finset_mem_Icc a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [lt_sub_iff_add_lt, Int.lt_add_one_iff, add_comm] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [← lt_add_one_iff] at hb
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ico a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      exact ⟨Int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ioc a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [← add_one_le_iff, le_sub_iff_add_le', add_comm _ (1 : ℤ), ← add_assoc] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, ← add_one_le_iff, sub_add, add_sub_cancel]
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ioo a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, add_left_embedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [sub_sub, lt_sub_iff_add_lt'] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, sub_sub]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩

namespace Int

variable (a b : ℤ)

theorem icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Icc_eq_finset_map Int.icc_eq_finset_map

theorem ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Ico_eq_finset_map Int.ico_eq_finset_map

theorem ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioc_eq_finset_map Int.ioc_eq_finset_map

theorem ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioo_eq_finset_map Int.ioo_eq_finset_map

@[simp]
theorem card_icc : (Icc a b).card = (b + 1 - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Icc Int.card_icc

@[simp]
theorem card_ico : (Ico a b).card = (b - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ico Int.card_ico

@[simp]
theorem card_ioc : (Ioc a b).card = (b - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ioc Int.card_ioc

@[simp]
theorem card_ioo : (Ioo a b).card = (b - a - 1).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ioo Int.card_ioo

theorem card_icc_of_le (h : a ≤ b + 1) : ((Icc a b).card : ℤ) = b + 1 - a := by
  rw [card_Icc, to_nat_sub_of_le h]
#align int.card_Icc_of_le Int.card_icc_of_le

theorem card_ico_of_le (h : a ≤ b) : ((Ico a b).card : ℤ) = b - a := by
  rw [card_Ico, to_nat_sub_of_le h]
#align int.card_Ico_of_le Int.card_ico_of_le

theorem card_ioc_of_le (h : a ≤ b) : ((Ioc a b).card : ℤ) = b - a := by
  rw [card_Ioc, to_nat_sub_of_le h]
#align int.card_Ioc_of_le Int.card_ioc_of_le

theorem card_ioo_of_lt (h : a < b) : ((Ioo a b).card : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, to_nat_sub_of_le h]
#align int.card_Ioo_of_lt Int.card_ioo_of_lt

@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = (b + 1 - a).toNat := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align int.card_fintype_Icc Int.card_fintypeIcc

@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = (b - a).toNat := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align int.card_fintype_Ico Int.card_fintypeIco

@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = (b - a).toNat := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align int.card_fintype_Ioc Int.card_fintypeIoc

@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = (b - a - 1).toNat := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align int.card_fintype_Ioo Int.card_fintypeIoo

theorem card_fintypeIcc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  rw [card_fintype_Icc, to_nat_sub_of_le h]
#align int.card_fintype_Icc_of_le Int.card_fintypeIcc_of_le

theorem card_fintypeIco_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  rw [card_fintype_Ico, to_nat_sub_of_le h]
#align int.card_fintype_Ico_of_le Int.card_fintypeIco_of_le

theorem card_fintypeIoc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  rw [card_fintype_Ioc, to_nat_sub_of_le h]
#align int.card_fintype_Ioc_of_le Int.card_fintypeIoc_of_le

theorem card_fintypeIoo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_fintype_Ioo, sub_sub, to_nat_sub_of_le h]
#align int.card_fintype_Ioo_of_lt Int.card_fintypeIoo_of_lt

theorem image_ico_mod (n a : ℤ) (h : 0 ≤ a) : (Ico n (n + a)).image (· % a) = Ico 0 a :=
  by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, exists_prop, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨mod_nonneg i (ne_of_gt ha), mod_lt_of_pos i ha⟩
  intro hia
  have hn := Int.mod_add_div n a
  obtain hi | hi := lt_or_le i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [zero_add] using add_le_add hia.left (Int.emod_lt_of_pos n ha).le
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine' add_lt_add_of_lt_of_le hia.right (le_trans _ hn.le)
      simp only [zero_le, le_add_iff_nonneg_left]
      exact Int.emod_nonneg n (ne_of_gt ha)
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
#align int.image_Ico_mod Int.image_ico_mod

end Int

