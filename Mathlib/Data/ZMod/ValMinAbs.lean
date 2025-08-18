/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-!
# Absolute value in `ZMod n`
-/

namespace ZMod
variable {n : ℕ} {a : ZMod n}

/-- Returns the integer in the same equivalence class as `x` that is closest to `0`.

The result will be in the interval `(-n/2, n/2]`. -/
def valMinAbs : ∀ {n : ℕ}, ZMod n → ℤ
  | 0, x => x
  | n@(_ + 1), x => if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n

@[simp] lemma valMinAbs_def_zero (x : ZMod 0) : valMinAbs x = x := rfl

lemma valMinAbs_def_pos : ∀ {n : ℕ} [NeZero n] (x : ZMod n),
    valMinAbs x = if x.val ≤ n / 2 then (x.val : ℤ) else x.val - n
  | 0, _, x => by cases NeZero.ne 0 rfl
  | n + 1, _, x => rfl

@[simp, norm_cast]
lemma coe_valMinAbs : ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, _ => Int.cast_id
  | k@(n + 1), x => by
    rw [valMinAbs_def_pos]
    split_ifs
    · rw [Int.cast_natCast, natCast_zmod_val]
    · rw [Int.cast_sub, Int.cast_natCast, natCast_zmod_val, Int.cast_natCast, natCast_self,
        sub_zero]

lemma injective_valMinAbs : (valMinAbs : ZMod n → ℤ).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩

lemma valMinAbs_nonneg_iff [NeZero n] (x : ZMod n) : 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2 := by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_ge h

lemma valMinAbs_mul_two_eq_iff (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n := by
  rcases n with - | n
  · simp
  by_cases h : a.val ≤ n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h, ← Int.natCast_inj, Nat.cast_mul, Nat.cast_two, mul_comm, Int.natCast_add,
      Nat.cast_one]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg_iff, ← mul_nonneg_iff_left_nonneg_of_pos, he] at h
    exacts [h (Nat.cast_nonneg _), zero_lt_two]
  · rw [mul_comm]
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le

lemma valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.valMinAbs * 2 ∈ Set.Ioc (-n : ℤ) n := by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · refine ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (mul_nonneg ?_ ?_), h⟩
    exacts [Nat.cast_nonneg _, zero_le_two]
  · refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) <| Nat.cast_nonneg _⟩
    · linarith only [h]
    · rw [sub_nonpos, Int.ofNat_le]
      exact x.val_lt.le

lemma valMinAbs_spec [NeZero n] (x : ZMod n) (y : ℤ) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n where
  mp := by rintro rfl; exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩
  mpr h := by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
    rw [← mul_lt_mul_right (@zero_lt_two ℤ _ _ _ _ _)]
    nth_rw 1 [← abs_eq_self.2 (@zero_le_two ℤ _ _ _ _)]
    rw [← abs_mul, sub_mul, abs_lt]
    constructor <;> linarith only [x.valMinAbs_mem_Ioc.1, x.valMinAbs_mem_Ioc.2, h.2.1, h.2.2]

lemma natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs ≤ n / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  rcases x.valMinAbs.natAbs_eq with h | h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le

@[simp]
lemma valMinAbs_zero : ∀ n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [valMinAbs_def_zero]
  | n + 1 => by simp only [valMinAbs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]

@[simp]
lemma valMinAbs_eq_zero (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 := by
  rcases n with - | n
  · simp
  rw [← valMinAbs_zero n.succ]
  apply injective_valMinAbs.eq_iff

lemma natCast_natAbs_valMinAbs [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a := by
  have : (a.val : ℤ) - n ≤ 0 := by
    rw [sub_nonpos, Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_natCast, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.cast_natCast, natCast_self, sub_zero, natCast_zmod_val]

lemma valMinAbs_neg_of_ne_half (ha : 2 * a.val ≠ n) : (-a).valMinAbs = -a.valMinAbs := by
  rcases eq_zero_or_neZero n with h | h
  · subst h
    rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]

@[simp]
lemma natAbs_valMinAbs_neg (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs := by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]

lemma val_eq_ite_valMinAbs [NeZero n] (a : ZMod n) :
    (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n := by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]

lemma prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne, natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd,
    ← hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

variable {n a : ℕ}

lemma valMinAbs_natAbs_eq_min [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) := by
  rw [valMinAbs_def_pos]
  have := a.val_lt
  omega

lemma valMinAbs_natCast_of_le_half (ha : a ≤ n / 2) : (a : ZMod n).valMinAbs = a := by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]

lemma valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) :
    (a : ZMod n).valMinAbs = a - n := by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_ge]

@[simp]
lemma valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a ≤ n / 2 := by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_natCast a, ← ha]
  exact natAbs_valMinAbs_le (n := n) a

lemma natAbs_valMinAbs_add_le (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs := by
  rcases n with - | n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le

end ZMod
