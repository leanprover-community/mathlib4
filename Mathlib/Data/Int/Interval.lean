/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

assert_not_exists Field

open Finset Int

namespace Int

instance instLocallyFiniteOrder : LocallyFiniteOrder ℤ where
  finsetIcc a b :=
    (Finset.range (b + 1 - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIco a b := (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIoc a b :=
    (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finsetIoo a b :=
    (Finset.range (b - a - 1).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finset_mem_Icc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · omega
    · intro
      use (x - a).toNat
      omega
  finset_mem_Ico a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · omega
    · intro
      use (x - a).toNat
      omega
  finset_mem_Ioc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · omega
    · intro
      use (x - (a + 1)).toNat
      omega
  finset_mem_Ioo a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · omega
    · intro
      use (x - (a + 1)).toNat
      omega

variable (a b : ℤ)

theorem Icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

theorem Ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

theorem Ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

theorem Ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

theorem uIcc_eq_finset_map :
    uIcc a b = (range (max a b + 1 - min a b).toNat).map
      (Nat.castEmbedding.trans <| addLeftEmbedding <| min a b) := rfl

@[simp]
theorem card_Icc : #(Icc a b) = (b + 1 - a).toNat := (card_map _).trans <| card_range _

@[simp]
theorem card_Ico : #(Ico a b) = (b - a).toNat := (card_map _).trans <| card_range _

@[simp]
theorem card_Ioc : #(Ioc a b) = (b - a).toNat := (card_map _).trans <| card_range _

@[simp]
theorem card_Ioo : #(Ioo a b) = (b - a - 1).toNat := (card_map _).trans <| card_range _

@[simp]
theorem card_uIcc : #(uIcc a b) = (b - a).natAbs + 1 :=
  (card_map _).trans <|
    (Nat.cast_inj (R := ℤ)).mp <| by
      rw [card_range,
        Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max), Int.natCast_add,
        Int.natCast_natAbs, add_comm, add_sub_assoc, max_sub_min_eq_abs, add_comm, Int.ofNat_one]

theorem card_Icc_of_le (h : a ≤ b + 1) : (#(Icc a b) : ℤ) = b + 1 - a := by
  rw [card_Icc, toNat_sub_of_le h]

theorem card_Ico_of_le (h : a ≤ b) : (#(Ico a b) : ℤ) = b - a := by
  rw [card_Ico, toNat_sub_of_le h]

theorem card_Ioc_of_le (h : a ≤ b) : (#(Ioc a b) : ℤ) = b - a := by
  rw [card_Ioc, toNat_sub_of_le h]

theorem card_Ioo_of_lt (h : a < b) : (#(Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, toNat_sub_of_le h]

theorem Icc_eq_pair : Finset.Icc a (a + 1) = {a, a + 1} := by
  ext
  simp
  omega

@[deprecated Fintype.card_Icc (since := "2025-03-28")]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = (b + 1 - a).toNat := by
  simp

@[deprecated Fintype.card_Ico (since := "2025-03-28")]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = (b - a).toNat := by
  simp

@[deprecated Fintype.card_Ioc (since := "2025-03-28")]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = (b - a).toNat := by
  simp

@[deprecated Fintype.card_Ioo (since := "2025-03-28")]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = (b - a - 1).toNat := by
  simp

@[deprecated Fintype.card_uIcc (since := "2025-03-28")]
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a).natAbs + 1 := by
  simp

theorem card_fintype_Icc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  simp [h]

theorem card_fintype_Ico_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  simp [h]

theorem card_fintype_Ioc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  simp [h]

theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  simp [h]

theorem image_Ico_emod (n a : ℤ) (h : 0 ≤ a) : (Ico n (n + a)).image (· % a) = Ico 0 a := by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
  intro hia
  have hn := Int.emod_add_ediv n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add hia.left (Int.emod_lt_of_pos n ha).le
    · refine lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine add_lt_add_of_lt_of_le hia.right (le_trans ?_ hn.le)
      simp only [le_add_iff_nonneg_left]
      exact Int.emod_nonneg n (ne_of_gt ha)
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]

end Int
