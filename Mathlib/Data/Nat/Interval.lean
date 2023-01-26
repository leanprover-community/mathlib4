/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.nat.interval
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `ordered_group`, `canonically_ordered_monoid` or `succ_order`
and subsequently be moved upstream to `data.finset.locally_finite`.
-/


open Finset Nat

instance : LocallyFiniteOrder ℕ
    where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range' _ _⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩
  finset_mem_Icc a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [add_tsub_cancel_of_le (Nat.lt_succ_of_le h).le, Nat.lt_succ_iff]
    · rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
  finset_mem_Ico a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [add_tsub_cancel_of_le h]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2.le)
  finset_mem_Ioc a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [← succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), Nat.lt_succ_iff, Nat.succ_le_iff]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.le.trans hx.2)
  finset_mem_Ioo a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range', ← tsub_add_eq_tsub_tsub]
    cases le_or_lt (a + 1) b
    · rw [add_tsub_cancel_of_le h, Nat.succ_le_iff]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)

variable (a b c : ℕ)

namespace Nat

theorem icc_eq_range' : icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Icc_eq_range' Nat.icc_eq_range'

theorem ico_eq_range' : ico a b = ⟨List.range' a (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ico_eq_range' Nat.ico_eq_range'

theorem ioc_eq_range' : ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioc_eq_range' Nat.ioc_eq_range'

theorem ioo_eq_range' : ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioo_eq_range' Nat.ioo_eq_range'

theorem iio_eq_range : Iio = range := by
  ext (b x)
  rw [mem_Iio, mem_range]
#align nat.Iio_eq_range Nat.iio_eq_range

@[simp]
theorem ico_zero_eq_range : ico 0 = range := by rw [← bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]
#align nat.Ico_zero_eq_range Nat.ico_zero_eq_range

theorem Finset.range_eq_ico : range = ico 0 :=
  ico_zero_eq_range.symm
#align finset.range_eq_Ico Finset.range_eq_ico

@[simp]
theorem card_icc : (icc a b).card = b + 1 - a :=
  List.length_range' _ _
#align nat.card_Icc Nat.card_icc

@[simp]
theorem card_ico : (ico a b).card = b - a :=
  List.length_range' _ _
#align nat.card_Ico Nat.card_ico

@[simp]
theorem card_ioc : (ioc a b).card = b - a :=
  List.length_range' _ _
#align nat.card_Ioc Nat.card_ioc

@[simp]
theorem card_ioo : (ioo a b).card = b - a - 1 :=
  List.length_range' _ _
#align nat.card_Ioo Nat.card_ioo

@[simp]
theorem card_iic : (iic b).card = b + 1 := by rw [Iic_eq_Icc, card_Icc, bot_eq_zero, tsub_zero]
#align nat.card_Iic Nat.card_iic

@[simp]
theorem card_iio : (iio b).card = b := by rw [Iio_eq_Ico, card_Ico, bot_eq_zero, tsub_zero]
#align nat.card_Iio Nat.card_iio

@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [Fintype.card_ofFinset, card_Icc]
#align nat.card_fintype_Icc Nat.card_fintypeIcc

@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ico]
#align nat.card_fintype_Ico Nat.card_fintypeIco

@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ioc]
#align nat.card_fintype_Ioc Nat.card_fintypeIoc

@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [Fintype.card_ofFinset, card_Ioo]
#align nat.card_fintype_Ioo Nat.card_fintypeIoo

@[simp]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align nat.card_fintype_Iic Nat.card_fintypeIic

@[simp]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by rw [Fintype.card_ofFinset, card_Iio]
#align nat.card_fintype_Iio Nat.card_fintypeIio

-- TODO@Yaël: Generalize all the following lemmas to `succ_order`
theorem icc_succ_left : icc a.succ b = ioc a b :=
  by
  ext x
  rw [mem_Icc, mem_Ioc, succ_le_iff]
#align nat.Icc_succ_left Nat.icc_succ_left

theorem ico_succ_right : ico a b.succ = icc a b :=
  by
  ext x
  rw [mem_Ico, mem_Icc, lt_succ_iff]
#align nat.Ico_succ_right Nat.ico_succ_right

theorem ico_succ_left : ico a.succ b = ioo a b :=
  by
  ext x
  rw [mem_Ico, mem_Ioo, succ_le_iff]
#align nat.Ico_succ_left Nat.ico_succ_left

theorem icc_pred_right {b : ℕ} (h : 0 < b) : icc a (b - 1) = ico a b :=
  by
  ext x
  rw [mem_Icc, mem_Ico, lt_iff_le_pred h]
#align nat.Icc_pred_right Nat.icc_pred_right

theorem ico_succ_succ : ico a.succ b.succ = ioc a b :=
  by
  ext x
  rw [mem_Ico, mem_Ioc, succ_le_iff, lt_succ_iff]
#align nat.Ico_succ_succ Nat.ico_succ_succ

@[simp]
theorem ico_succ_singleton : ico a (a + 1) = {a} := by rw [Ico_succ_right, Icc_self]
#align nat.Ico_succ_singleton Nat.ico_succ_singleton

@[simp]
theorem ico_pred_singleton {a : ℕ} (h : 0 < a) : ico (a - 1) a = {a - 1} := by
  rw [← Icc_pred_right _ h, Icc_self]
#align nat.Ico_pred_singleton Nat.ico_pred_singleton

@[simp]
theorem ioc_succ_singleton : ioc b (b + 1) = {b + 1} := by rw [← Nat.icc_succ_left, Icc_self]
#align nat.Ioc_succ_singleton Nat.ioc_succ_singleton

variable {a b c}

theorem ico_succ_right_eq_insert_ico (h : a ≤ b) : ico a (b + 1) = insert b (ico a b) := by
  rw [Ico_succ_right, ← Ico_insert_right h]
#align nat.Ico_succ_right_eq_insert_Ico Nat.ico_succ_right_eq_insert_ico

theorem ico_insert_succ_left (h : a < b) : insert a (ico a.succ b) = ico a b := by
  rw [Ico_succ_left, ← Ioo_insert_left h]
#align nat.Ico_insert_succ_left Nat.ico_insert_succ_left

theorem image_sub_const_ico (h : c ≤ a) : ((ico a b).image fun x => x - c) = ico (a - c) (b - c) :=
  by
  ext x
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx⊢
    exact ⟨tsub_le_tsub_right hx.1 _, tsub_lt_tsub_right_of_le (h.trans hx.1) hx.2⟩
  · rintro h
    refine' ⟨x + c, _, add_tsub_cancel_right _ _⟩
    rw [mem_Ico] at h⊢
    exact ⟨tsub_le_iff_right.1 h.1, lt_tsub_iff_right.1 h.2⟩
#align nat.image_sub_const_Ico Nat.image_sub_const_ico

theorem ico_image_const_sub_eq_ico (hac : a ≤ c) :
    ((ico a b).image fun x => c - x) = ico (c + 1 - b) (c + 1 - a) :=
  by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx
    refine'
      ⟨_,
        ((tsub_le_tsub_iff_left hac).2 hx.1).trans_lt
          ((tsub_lt_tsub_iff_right hac).2 (Nat.lt_succ_self _))⟩
    cases lt_or_le c b
    · rw [tsub_eq_zero_iff_le.mpr (succ_le_of_lt h)]
      exact zero_le _
    · rw [← succ_sub_succ c]
      exact (tsub_le_tsub_iff_left (succ_le_succ <| hx.2.le.trans h)).2 hx.2
  · rintro ⟨hb, ha⟩
    rw [lt_tsub_iff_left, lt_succ_iff] at ha
    have hx : x ≤ c := (Nat.le_add_left _ _).trans ha
    refine' ⟨c - x, _, tsub_tsub_cancel_of_le hx⟩
    · rw [mem_Ico]
      exact
        ⟨le_tsub_of_add_le_right ha,
          (tsub_lt_iff_left hx).2 <| succ_le_iff.1 <| tsub_le_iff_right.1 hb⟩
#align nat.Ico_image_const_sub_eq_Ico Nat.ico_image_const_sub_eq_ico

theorem ico_succ_left_eq_erase_ico : ico a.succ b = erase (ico a b) a :=
  by
  ext x
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ← and_assoc', ne_comm, and_comm' (a ≠ x),
    lt_iff_le_and_ne]
#align nat.Ico_succ_left_eq_erase_Ico Nat.ico_succ_left_eq_erase_ico

theorem mod_injOn_ico (n a : ℕ) : Set.InjOn (· % a) (Finset.ico n (n + a)) :=
  by
  induction' n with n ih
  · simp only [zero_add, nat_zero_eq_zero, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  rw [Ico_succ_left_eq_erase_Ico, succ_add, Ico_succ_right_eq_insert_Ico le_self_add]
  rintro k hk l hl (hkl : k % a = l % a)
  have ha : 0 < a := by
    by_contra ha
    simp only [not_lt, nonpos_iff_eq_zero] at ha
    simpa [ha] using hk
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
  rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
  · rfl
  · rw [add_mod_right] at hkl
    refine' (hln <| ih hl _ hkl.symm).elim
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_ico, ha]
  · rw [add_mod_right] at hkl
    suffices k = n by contradiction
    refine' ih hk _ hkl
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_ico, ha]
  · refine' ih _ _ hkl <;> simp only [Finset.mem_coe, hk, hl]
#align nat.mod_inj_on_Ico Nat.mod_injOn_ico

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `int.image_Ico_mod` for the ℤ version. -/
theorem image_ico_mod (n a : ℕ) : (ico n (n + a)).image (· % a) = range a :=
  by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, exists_prop, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_le i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine' add_lt_add_of_lt_of_le hia (le_trans _ hn.le)
      simp only [zero_le, le_add_iff_nonneg_left]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
#align nat.image_Ico_mod Nat.image_ico_mod

section Multiset

open Multiset

theorem multiset_ico_map_mod (n a : ℕ) : (Multiset.ico n (n + a)).map (· % a) = range a :=
  by
  convert congr_arg Finset.val (image_Ico_mod n a)
  refine' ((nodup_map_iff_inj_on (Finset.ico _ _).Nodup).2 <| _).dedup.symm
  exact mod_inj_on_Ico _ _
#align nat.multiset_Ico_map_mod Nat.multiset_ico_map_mod

end Multiset

end Nat

namespace Finset

theorem range_image_pred_top_sub (n : ℕ) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n :=
  by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_ico, Nat.ico_image_const_sub_eq_ico (zero_le _)]
    simp_rw [succ_sub_succ, tsub_zero, tsub_self]
#align finset.range_image_pred_top_sub Finset.range_image_pred_top_sub

theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) :=
  by
  rw [Finset.range_eq_ico, map_eq_image]
  convert (Ico_union_Ico_eq_Ico a.zero_le le_self_add).symm
  exact image_add_left_Ico _ _ _
#align finset.range_add_eq_union Finset.range_add_eq_union

end Finset

section Induction

variable {P : ℕ → Prop} (h : ∀ n, P (n + 1) → P n)

include h

theorem Nat.decreasing_induction_of_not_bddAbove (hP : ¬BddAbove { x | P x }) (n : ℕ) : P n :=
  let ⟨m, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction h hl.le hm
#align nat.decreasing_induction_of_not_bdd_above Nat.decreasing_induction_of_not_bddAbove

theorem Nat.decreasing_induction_of_infinite (hP : { x | P x }.Infinite) (n : ℕ) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n
#align nat.decreasing_induction_of_infinite Nat.decreasing_induction_of_infinite

theorem Nat.cauchy_induction' (seed : ℕ) (hs : P seed) (hi : ∀ x, seed ≤ x → P x → ∃ y, x < y ∧ P y)
    (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal_wrt id _ ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_lt fun hl => hl.Ne <| hm seed hs hl.le) hP
  exact hl.ne (hm y hy hl.le)
#align nat.cauchy_induction' Nat.cauchy_induction'

theorem Nat.cauchy_induction (seed : ℕ) (hs : P seed) (f : ℕ → ℕ)
    (hf : ∀ x, seed ≤ x → P x → x < f x ∧ P (f x)) (n : ℕ) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n
#align nat.cauchy_induction Nat.cauchy_induction

theorem Nat.cauchy_induction_mul (k seed : ℕ) (hk : 1 < k) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (k * x)) (n : ℕ) : P n :=
  by
  apply Nat.cauchy_induction h _ hs ((· * ·) k) fun x hl hP => ⟨_, hm x hl hP⟩
  convert (mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]
#align nat.cauchy_induction_mul Nat.cauchy_induction_mul

theorem Nat.cauchy_induction_two_mul (seed : ℕ) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (2 * x)) (n : ℕ) : P n :=
  Nat.cauchy_induction_mul h 2 seed one_lt_two hs hm n
#align nat.cauchy_induction_two_mul Nat.cauchy_induction_two_mul

end Induction

