/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Order.Interval.Multiset

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `OrderedGroup`, `CanonicallyOrderedMul` or `SuccOrder`
and subsequently be moved upstream to `Order.Interval.Finset`.
-/

assert_not_exists Ring

open Finset Nat

variable (a b c : ℕ)

namespace Nat

instance instLocallyFiniteOrder : LocallyFiniteOrder ℕ where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range'⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  finset_mem_Icc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; omega
  finset_mem_Ico a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; omega
  finset_mem_Ioc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; omega
  finset_mem_Ioo a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; omega

theorem Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range'⟩ :=
  rfl

theorem Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range'⟩ :=
  rfl

theorem Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩ :=
  rfl

theorem Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩ :=
  rfl

theorem uIcc_eq_range' :
    uIcc a b = ⟨List.range' (min a b) (max a b + 1 - min a b), List.nodup_range'⟩ := rfl

theorem Iio_eq_range : Iio = range := by
  ext b x
  rw [mem_Iio, mem_range]

@[simp]
theorem Ico_zero_eq_range : Ico 0 = range := by rw [← Nat.bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]

lemma range_eq_Icc_zero_sub_one (n : ℕ) (hn : n ≠ 0) : range n = Icc 0 (n - 1) := by
  ext b
  simp_all only [mem_Icc, zero_le, true_and, mem_range]
  exact lt_iff_le_pred (zero_lt_of_ne_zero hn)

theorem _root_.Finset.range_eq_Ico : range = Ico 0 :=
  Ico_zero_eq_range.symm

theorem range_succ_eq_Icc_zero (n : ℕ) : range (n + 1) = Icc 0 n := by
  rw [range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _), Nat.add_sub_cancel_right]

@[simp] lemma card_Icc : #(Icc a b) = b + 1 - a := List.length_range' ..
@[simp] lemma card_Ico : #(Ico a b) = b - a := List.length_range' ..
@[simp] lemma card_Ioc : #(Ioc a b) = b - a := List.length_range' ..
@[simp] lemma card_Ioo : #(Ioo a b) = b - a - 1 := List.length_range' ..

@[simp]
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 :=
  (card_Icc _ _).trans <| by rw [← Int.natCast_inj, Int.ofNat_sub] <;> omega

@[simp]
lemma card_Iic : #(Iic b) = b + 1 := by rw [Iic_eq_Icc, card_Icc, Nat.bot_eq_zero, Nat.sub_zero]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [Iio_eq_Ico, card_Ico, Nat.bot_eq_zero, Nat.sub_zero]

@[deprecated Fintype.card_Icc (since := "2025-03-28")]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by simp

@[deprecated Fintype.card_Ico (since := "2025-03-28")]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by simp

@[deprecated Fintype.card_Ioc (since := "2025-03-28")]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by simp

@[deprecated Fintype.card_Ioo (since := "2025-03-28")]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by simp

@[deprecated Fintype.card_Iic (since := "2025-03-28")]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by simp

@[deprecated Fintype.card_Iio (since := "2025-03-28")]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by simp

@[deprecated Finset.Icc_succ_left_eq_Ioc (since := "2025-04-24")]
theorem Icc_succ_left : Icc a.succ b = Ioc a b := by
  ext x
  rw [mem_Icc, mem_Ioc, succ_le_iff]

@[deprecated Finset.Ico_succ_right_eq_Icc (since := "2025-04-24")]
theorem Ico_succ_right : Ico a b.succ = Icc a b := by
  ext x
  rw [mem_Ico, mem_Icc, Nat.lt_succ_iff]

@[deprecated Finset.Ico_succ_left_eq_Ioo (since := "2025-04-24")]
theorem Ico_succ_left : Ico a.succ b = Ioo a b := by
  ext x
  rw [mem_Ico, mem_Ioo, succ_le_iff]

@[deprecated Finset.Icc_pred_right_eq_Ico (since := "2025-04-24")]
theorem Icc_pred_right {b : ℕ} (h : 0 < b) : Icc a (b - 1) = Ico a b := by
  ext x
  rw [mem_Icc, mem_Ico, lt_iff_le_pred h]

@[deprecated Finset.Ico_succ_succ_eq_Ioc (since := "2025-04-24")]
theorem Ico_succ_succ : Ico a.succ b.succ = Ioc a b := by
  ext x
  rw [mem_Ico, mem_Ioc, succ_le_iff, Nat.lt_succ_iff]

-- TODO: Generalise the following series of lemmas.

set_option linter.deprecated false in
@[simp]
theorem Ico_succ_singleton : Ico a (a + 1) = {a} := by rw [Ico_succ_right, Icc_self]

set_option linter.deprecated false in
@[simp]
theorem Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} := by
  rw [← Icc_pred_right _ h, Icc_self]

set_option linter.deprecated false in
@[simp]
theorem Ioc_succ_singleton : Ioc b (b + 1) = {b + 1} := by rw [← Nat.Icc_succ_left, Icc_self]

variable {a b c}

lemma mem_Ioc_succ : a ∈ Ioc b (b + 1) ↔ a = b + 1 := by simp

lemma mem_Ioc_succ' (a : Ioc b (b + 1)) : a = ⟨b + 1, mem_Ioc.2 (by omega)⟩ :=
  Subtype.val_inj.1 (mem_Ioc_succ.1 a.2)

set_option linter.deprecated false in
@[deprecated Finset.insert_Ico_right_eq_Ico_succ_right (since := "2025-04-24")]
theorem Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) := by
  rw [Ico_succ_right, ← Ico_insert_right h]

set_option linter.deprecated false in
@[deprecated Finset.insert_Ico_succ_left_eq_Ico (since := "2025-04-24")]
theorem Ico_insert_succ_left (h : a < b) : insert a (Ico a.succ b) = Ico a b := by
  rw [Ico_succ_left, ← Ioo_insert_left h]

@[deprecated Finset.insert_Icc_succ_left_eq_Icc (since := "2025-04-24")]
lemma Icc_insert_succ_left (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

@[deprecated Finset.insert_Icc_eq_Icc_succ_right (since := "2025-04-24")]
lemma Icc_insert_succ_right (h : a ≤ b + 1) : insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

theorem image_sub_const_Ico (h : c ≤ a) :
    ((Ico a b).image fun x => x - c) = Ico (a - c) (b - c) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h ↦ ⟨x + c, by omega⟩⟩
  rintro ⟨x, hx, rfl⟩
  omega

theorem Ico_image_const_sub_eq_Ico (hac : a ≤ c) :
    ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h ↦ ⟨c - x, by omega⟩⟩
  rintro ⟨x, hx, rfl⟩
  omega

set_option linter.deprecated false in
theorem Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a := by
  ext x
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ← and_assoc, ne_comm,
    and_comm (a := a ≠ x), lt_iff_le_and_ne]

set_option linter.deprecated false in
theorem mod_injOn_Ico (n a : ℕ) : Set.InjOn (· % a) (Finset.Ico n (n + a)) := by
  induction n with
  | zero =>
    simp only [zero_add, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  | succ n ih =>
    rw [Ico_succ_left_eq_erase_Ico, succ_add, succ_eq_add_one,
      Ico_succ_right_eq_insert_Ico (by omega)]
    rintro k hk l hl (hkl : k % a = l % a)
    have ha : 0 < a := Nat.pos_iff_ne_zero.2 <| by rintro rfl; simp at hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
    rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
    · rfl
    · rw [add_mod_right] at hkl
      refine (hln <| ih hl ?_ hkl.symm).elim
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · rw [add_mod_right] at hkl
      suffices k = n by contradiction
      refine ih hk ?_ hkl
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · refine ih ?_ ?_ hkl <;> simp only [Finset.mem_coe, hk, hl]

/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `Int.image_Ico_emod` for the ℤ version. -/
theorem image_Ico_mod (n a : ℕ) : (Ico n (n + a)).image (· % a) = range a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), Nat.mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (Nat.add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine lt_of_lt_of_le (Nat.add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [Nat.mul_add, mul_one, ← add_assoc, hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]

section Multiset

open Multiset

theorem multiset_Ico_map_mod (n a : ℕ) :
    (Multiset.Ico n (n + a)).map (· % a) = Multiset.range a := by
  convert congr_arg Finset.val (image_Ico_mod n a)
  refine ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| ?_).dedup.symm
  exact mod_injOn_Ico _ _

end Multiset

end Nat

namespace List

lemma toFinset_range'_1 (a b : ℕ) : (List.range' a b).toFinset = Ico a (a + b) := by
  ext x
  rw [List.mem_toFinset, List.mem_range'_1, Finset.mem_Ico]

lemma toFinset_range'_1_1 (a : ℕ) : (List.range' 1 a).toFinset = Icc 1 a := by
  ext x
  rw [List.mem_toFinset, List.mem_range'_1, add_comm, Nat.lt_succ_iff, Finset.mem_Icc]

lemma toFinset_range (a : ℕ) : (List.range a).toFinset = Finset.range a := by
  ext x
  rw [List.mem_toFinset, List.mem_range, Finset.mem_range]

end List

namespace Finset

theorem range_image_pred_top_sub (n : ℕ) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n := by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, Nat.sub_zero, Nat.sub_self]

theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [Finset.range_eq_Ico, map_eq_image]
  convert (Ico_union_Ico_eq_Ico a.zero_le (a.le_add_right b)).symm
  ext x
  simp only [Ico_zero_eq_range, mem_image, mem_range, addLeftEmbedding_apply, mem_Ico]
  constructor
  · aesop
  · rintro h
    exact ⟨x - a, by omega⟩

end Finset

section Induction

variable {P : ℕ → Prop}

theorem Nat.decreasing_induction_of_not_bddAbove (h : ∀ n, P (n + 1) → P n)
    (hP : ¬BddAbove { x | P x }) (n : ℕ) : P n :=
  let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction (fun _ _ => h _) hm hl.le

@[elab_as_elim]
lemma Nat.strong_decreasing_induction (base : ∃ n, ∀ m > n, P m) (step : ∀ n, (∀ m > n, P m) → P n)
    (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_not_bddAbove (P := fun n ↦ ∀ m ≥ n, P m) _ _ n n le_rfl
  · intro n ih m hm
    rcases hm.eq_or_lt with rfl | hm
    · exact step n ih
    · exact ih m hm
  · rintro ⟨b, hb⟩
    rcases base with ⟨n, hn⟩
    specialize @hb (n + b + 1) (fun m hm ↦ hn _ _)
    all_goals omega

theorem Nat.decreasing_induction_of_infinite
    (h : ∀ n, P (n + 1) → P n) (hP : { x | P x }.Infinite) (n : ℕ) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n

theorem Nat.cauchy_induction' (seed : ℕ) (h : ∀ n, P (n + 1) → P n) (hs : P seed)
    (hi : ∀ x, seed ≤ x → P x → ∃ y, x < y ∧ P y) (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_gt <| not_lt_iff_le_imp_ge.2 <| hm hs) hP
  exact hl.not_ge (hm hy hl.le)

theorem Nat.cauchy_induction (h : ∀ n, P (n + 1) → P n) (seed : ℕ) (hs : P seed) (f : ℕ → ℕ)
    (hf : ∀ x, seed ≤ x → P x → x < f x ∧ P (f x)) (n : ℕ) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n

theorem Nat.cauchy_induction_mul (h : ∀ (n : ℕ), P (n + 1) → P n) (k seed : ℕ) (hk : 1 < k)
    (hs : P seed.succ) (hm : ∀ x, seed < x → P x → P (k * x)) (n : ℕ) : P n := by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert (Nat.mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]

theorem Nat.cauchy_induction_two_mul (h : ∀ n, P (n + 1) → P n) (seed : ℕ) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (2 * x)) (n : ℕ) : P n :=
  Nat.cauchy_induction_mul h 2 seed Nat.one_lt_two hs hm n

theorem Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k : ℕ) (hk : 1 < k)
    (P : M → Prop) (hmul : ∀ x y, P x → P (x * y) ∨ P (y * x))
    (hpow : ∀ x, P (x ^ k) → P x) : ∀ n x, P (x ^ n) → P x :=
  k.cauchy_induction_mul (fun n ih x hx ↦ ih x <| (hmul _ x hx).elim
    (fun h ↦ by rwa [_root_.pow_succ]) fun h ↦ by rwa [_root_.pow_succ']) 0 hk
    (fun x hx ↦ pow_one x ▸ hx) fun n _ hn x hx ↦ hpow x <| hn _ <| (pow_mul x k n).subst hx

end Induction
