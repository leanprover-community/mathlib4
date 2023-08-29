/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Finset.LocallyFinite

#align_import data.int.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `LocallyFiniteOrder` and calculates the cardinality of its
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
  finset_mem_Icc a b x := by
    simp_rw [mem_map, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    -- ⊢ (∃ a_1, ↑a_1 < b + 1 - a ∧ a + ↑a_1 = x) → a ≤ x ∧ x ≤ b
    · rintro ⟨a, h, rfl⟩
      -- ⊢ a✝ ≤ a✝ + ↑a ∧ a✝ + ↑a ≤ b
      rw [lt_sub_iff_add_lt, Int.lt_add_one_iff, add_comm] at h
      -- ⊢ a✝ ≤ a✝ + ↑a ∧ a✝ + ↑a ≤ b
      exact ⟨Int.le.intro a rfl, h⟩
      -- 🎉 no goals
    · rintro ⟨ha, hb⟩
      -- ⊢ ∃ a_1, ↑a_1 < b + 1 - a ∧ a + ↑a_1 = x
      use (x - a).toNat
      -- ⊢ ↑(toNat (x - a)) < b + 1 - a ∧ a + ↑(toNat (x - a)) = x
      rw [← lt_add_one_iff] at hb
      -- ⊢ ↑(toNat (x - a)) < b + 1 - a ∧ a + ↑(toNat (x - a)) = x
      rw [toNat_sub_of_le ha]
      -- ⊢ x - a < b + 1 - a ∧ a + (x - a) = x
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      -- 🎉 no goals
  finset_mem_Ico a b x := by
    simp_rw [mem_map, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    -- ⊢ (∃ a_1, ↑a_1 < b - a ∧ a + ↑a_1 = x) → a ≤ x ∧ x < b
    · rintro ⟨a, h, rfl⟩
      -- ⊢ a✝ ≤ a✝ + ↑a ∧ a✝ + ↑a < b
      exact ⟨Int.le.intro a rfl, lt_sub_iff_add_lt'.mp h⟩
      -- 🎉 no goals
    · rintro ⟨ha, hb⟩
      -- ⊢ ∃ a_1, ↑a_1 < b - a ∧ a + ↑a_1 = x
      use (x - a).toNat
      -- ⊢ ↑(toNat (x - a)) < b - a ∧ a + ↑(toNat (x - a)) = x
      rw [toNat_sub_of_le ha]
      -- ⊢ x - a < b - a ∧ a + (x - a) = x
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      -- 🎉 no goals
  finset_mem_Ioc a b x := by
    simp_rw [mem_map, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    -- ⊢ (∃ a_1, ↑a_1 < b - a ∧ a + 1 + ↑a_1 = x) → a < x ∧ x ≤ b
    · rintro ⟨a, h, rfl⟩
      -- ⊢ a✝ < a✝ + 1 + ↑a ∧ a✝ + 1 + ↑a ≤ b
      rw [← add_one_le_iff, le_sub_iff_add_le', add_comm _ (1 : ℤ), ← add_assoc] at h
      -- ⊢ a✝ < a✝ + 1 + ↑a ∧ a✝ + 1 + ↑a ≤ b
      exact ⟨Int.le.intro a rfl, h⟩
      -- 🎉 no goals
    · rintro ⟨ha, hb⟩
      -- ⊢ ∃ a_1, ↑a_1 < b - a ∧ a + 1 + ↑a_1 = x
      use (x - (a + 1)).toNat
      -- ⊢ ↑(toNat (x - (a + 1))) < b - a ∧ a + 1 + ↑(toNat (x - (a + 1))) = x
      rw [toNat_sub_of_le ha, ← add_one_le_iff, sub_add, add_sub_cancel]
      -- ⊢ x - a ≤ b - a ∧ a + 1 + (x - (a + 1)) = x
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩
      -- 🎉 no goals
  finset_mem_Ioo a b x := by
    simp_rw [mem_map, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    -- ⊢ (∃ a_1, ↑a_1 < b - a - 1 ∧ a + 1 + ↑a_1 = x) → a < x ∧ x < b
    · rintro ⟨a, h, rfl⟩
      -- ⊢ a✝ < a✝ + 1 + ↑a ∧ a✝ + 1 + ↑a < b
      rw [sub_sub, lt_sub_iff_add_lt'] at h
      -- ⊢ a✝ < a✝ + 1 + ↑a ∧ a✝ + 1 + ↑a < b
      exact ⟨Int.le.intro a rfl, h⟩
      -- 🎉 no goals
    · rintro ⟨ha, hb⟩
      -- ⊢ ∃ a_1, ↑a_1 < b - a - 1 ∧ a + 1 + ↑a_1 = x
      use (x - (a + 1)).toNat
      -- ⊢ ↑(toNat (x - (a + 1))) < b - a - 1 ∧ a + 1 + ↑(toNat (x - (a + 1))) = x
      rw [toNat_sub_of_le ha, sub_sub]
      -- ⊢ x - (a + 1) < b - (a + 1) ∧ a + 1 + (x - (a + 1)) = x
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
      -- 🎉 no goals

namespace Int

variable (a b : ℤ)

theorem Icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Icc_eq_finset_map Int.Icc_eq_finset_map

theorem Ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Ico_eq_finset_map Int.Ico_eq_finset_map

theorem Ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioc_eq_finset_map Int.Ioc_eq_finset_map

theorem Ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioo_eq_finset_map Int.Ioo_eq_finset_map

theorem uIcc_eq_finset_map :
    uIcc a b = (range (max a b + 1 - min a b).toNat).map
      (Nat.castEmbedding.trans <| addLeftEmbedding $ min a b) := rfl
#align int.uIcc_eq_finset_map Int.uIcc_eq_finset_map

@[simp]
theorem card_Icc : (Icc a b).card = (b + 1 - a).toNat := (card_map _).trans $ card_range _
#align int.card_Icc Int.card_Icc

@[simp]
theorem card_Ico : (Ico a b).card = (b - a).toNat := (card_map _).trans $ card_range _
#align int.card_Ico Int.card_Ico

@[simp]
theorem card_Ioc : (Ioc a b).card = (b - a).toNat := (card_map _).trans $ card_range _
#align int.card_Ioc Int.card_Ioc

@[simp]
theorem card_Ioo : (Ioo a b).card = (b - a - 1).toNat := (card_map _).trans $ card_range _
#align int.card_Ioo Int.card_Ioo

@[simp]
theorem card_uIcc : (uIcc a b).card = (b - a).natAbs + 1 :=
  (card_map _).trans <|
    Int.ofNat.inj <| by
      -- porting note: TODO: Restore `int.coe_nat_inj` and remove the `change`
      change ((↑) : ℕ → ℤ) _ = ((↑) : ℕ → ℤ) _
      -- ⊢ ↑(card (range (toNat (a ⊔ b + 1 - a ⊓ b)))) = ↑(natAbs (b - a) + 1)
      rw [card_range, sup_eq_max, inf_eq_min,
        Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max), Int.ofNat_add,
        Int.coe_natAbs, add_comm, add_sub_assoc, max_sub_min_eq_abs, add_comm, Int.ofNat_one]
#align int.card_uIcc Int.card_uIcc

theorem card_Icc_of_le (h : a ≤ b + 1) : ((Icc a b).card : ℤ) = b + 1 - a := by
  rw [card_Icc, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_Icc_of_le Int.card_Icc_of_le

theorem card_Ico_of_le (h : a ≤ b) : ((Ico a b).card : ℤ) = b - a := by
  rw [card_Ico, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_Ico_of_le Int.card_Ico_of_le

theorem card_Ioc_of_le (h : a ≤ b) : ((Ioc a b).card : ℤ) = b - a := by
  rw [card_Ioc, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_Ioc_of_le Int.card_Ioc_of_le

theorem card_Ioo_of_lt (h : a < b) : ((Ioo a b).card : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_Ioo_of_lt Int.card_Ioo_of_lt

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = (b + 1 - a).toNat := by
  rw [← card_Icc, Fintype.card_ofFinset]
  -- 🎉 no goals
#align int.card_fintype_Icc Int.card_fintype_Icc

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = (b - a).toNat := by
  rw [← card_Ico, Fintype.card_ofFinset]
  -- 🎉 no goals
#align int.card_fintype_Ico Int.card_fintype_Ico

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = (b - a).toNat := by
  rw [← card_Ioc, Fintype.card_ofFinset]
  -- 🎉 no goals
#align int.card_fintype_Ioc Int.card_fintype_Ioc

-- porting note: removed `simp` attribute because `simpNF` says it can prove it
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = (b - a - 1).toNat := by
  rw [← card_Ioo, Fintype.card_ofFinset]
  -- 🎉 no goals
#align int.card_fintype_Ioo Int.card_fintype_Ioo

theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a).natAbs + 1 := by
  rw [← card_uIcc, Fintype.card_ofFinset]
  -- 🎉 no goals
#align int.card_fintype_uIcc Int.card_fintype_uIcc

theorem card_fintype_Icc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  rw [card_fintype_Icc, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_fintype_Icc_of_le Int.card_fintype_Icc_of_le

theorem card_fintype_Ico_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  rw [card_fintype_Ico, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_fintype_Ico_of_le Int.card_fintype_Ico_of_le

theorem card_fintype_Ioc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  rw [card_fintype_Ioc, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_fintype_Ioc_of_le Int.card_fintype_Ioc_of_le

theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_fintype_Ioo, sub_sub, toNat_sub_of_le h]
  -- 🎉 no goals
#align int.card_fintype_Ioo_of_lt Int.card_fintype_Ioo_of_lt

theorem image_Ico_emod (n a : ℤ) (h : 0 ≤ a) : (Ico n (n + a)).image (· % a) = Ico 0 a := by
  obtain rfl | ha := eq_or_lt_of_le h
  -- ⊢ image (fun x => x % 0) (Ico n (n + 0)) = Ico 0 0
  · simp
    -- 🎉 no goals
  ext i
  -- ⊢ i ∈ image (fun x => x % a) (Ico n (n + a)) ↔ i ∈ Ico 0 a
  simp only [mem_image, mem_range, mem_Ico]
  -- ⊢ (∃ a_1, (n ≤ a_1 ∧ a_1 < n + a) ∧ a_1 % a = i) ↔ 0 ≤ i ∧ i < a
  constructor
  -- ⊢ (∃ a_1, (n ≤ a_1 ∧ a_1 < n + a) ∧ a_1 % a = i) → 0 ≤ i ∧ i < a
  · rintro ⟨i, _, rfl⟩
    -- ⊢ 0 ≤ i % a ∧ i % a < a
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
    -- 🎉 no goals
  intro hia
  -- ⊢ ∃ a_1, (n ≤ a_1 ∧ a_1 < n + a) ∧ a_1 % a = i
  have hn := Int.emod_add_ediv n a
  -- ⊢ ∃ a_1, (n ≤ a_1 ∧ a_1 < n + a) ∧ a_1 % a = i
  obtain hi | hi := lt_or_le i (n % a)
  -- ⊢ ∃ a_1, (n ≤ a_1 ∧ a_1 < n + a) ∧ a_1 % a = i
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      -- ⊢ n ≤ i + a + a * (n / a)
      refine' hn.symm.le.trans (add_le_add_right _ _)
      -- ⊢ n % a ≤ i + a
      simpa only [zero_add] using add_le_add hia.left (Int.emod_lt_of_pos n ha).le
      -- 🎉 no goals
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      -- ⊢ n % a + a * (n / a + 1) ≤ n + a
      rw [mul_add, mul_one, ← add_assoc, hn]
      -- 🎉 no goals
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
      -- 🎉 no goals
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
      -- 🎉 no goals
    · rw [add_comm n a]
      -- ⊢ i + a * (n / a) < a + n
      refine' add_lt_add_of_lt_of_le hia.right (le_trans _ hn.le)
      -- ⊢ a * (n / a) ≤ n % a + a * (n / a)
      simp only [zero_le, le_add_iff_nonneg_left]
      -- ⊢ 0 ≤ n % a
      exact Int.emod_nonneg n (ne_of_gt ha)
      -- 🎉 no goals
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
      -- 🎉 no goals
#align int.image_Ico_mod Int.image_Ico_emod

end Int
