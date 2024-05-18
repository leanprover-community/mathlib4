/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Bitwise
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Basic

#align_import data.int.lemmas from "leanprover-community/mathlib"@"09597669f02422ed388036273d8848119699c22f"

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`Data.Int.Basic` or `Data.Int.Order`.

-/


open Nat

namespace Int

theorem le_natCast_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) := by
  by_cases h : m ≥ n
  · exact le_of_eq (Int.ofNat_sub h).symm
  · simp [le_of_not_ge h, ofNat_le]
#align int.le_coe_nat_sub Int.le_natCast_sub

/-! ### `succ` and `pred` -/


-- Porting note (#10618): simp can prove this @[simp]
theorem succ_natCast_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)
#align int.succ_coe_nat_pos Int.succ_natCast_pos

/-! ### `natAbs` -/


variable {a b : ℤ} {n : ℕ}

theorem natAbs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq, sq]
  exact natAbs_eq_iff_mul_self_eq
#align int.nat_abs_eq_iff_sq_eq Int.natAbs_eq_iff_sq_eq

theorem natAbs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq, sq]
  exact natAbs_lt_iff_mul_self_lt
#align int.nat_abs_lt_iff_sq_lt Int.natAbs_lt_iff_sq_lt

theorem natAbs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact natAbs_le_iff_mul_self_le
#align int.nat_abs_le_iff_sq_le Int.natAbs_le_iff_sq_le

theorem natAbs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq ha hb, ← natAbs_eq_iff_sq_eq]
#align int.nat_abs_inj_of_nonneg_of_nonneg Int.natAbs_inj_of_nonneg_of_nonneg

theorem natAbs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)
#align int.nat_abs_inj_of_nonpos_of_nonpos Int.natAbs_inj_of_nonpos_of_nonpos

theorem natAbs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)
#align int.nat_abs_inj_of_nonneg_of_nonpos Int.natAbs_inj_of_nonneg_of_nonpos

theorem natAbs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb
#align int.nat_abs_inj_of_nonpos_of_nonneg Int.natAbs_inj_of_nonpos_of_nonneg

/-- A specialization of `abs_sub_le_of_nonneg_of_le` for working with the signed subtraction
  of natural numbers. -/
theorem natAbs_coe_sub_coe_le_of_le {a b n : ℕ} (a_le_n : a ≤ n) (b_le_n : b ≤ n) :
    natAbs (a - b : ℤ) ≤ n := by
  rw [← Nat.cast_le (α := ℤ), natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (ofNat_nonneg a) (ofNat_le.mpr a_le_n)
    (ofNat_nonneg b) (ofNat_le.mpr b_le_n)

/-- A specialization of `abs_sub_lt_of_nonneg_of_lt` for working with the signed subtraction
  of natural numbers. -/
theorem natAbs_coe_sub_coe_lt_of_lt {a b n : ℕ} (a_lt_n : a < n) (b_lt_n : b < n) :
    natAbs (a - b : ℤ) < n := by
  rw [← Nat.cast_lt (α := ℤ), natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (ofNat_nonneg a) (ofNat_lt.mpr a_lt_n)
    (ofNat_nonneg b) (ofNat_lt.mpr b_lt_n)

section Intervals

open Set

theorem strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0) := fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab
#align int.strict_mono_on_nat_abs Int.strictMonoOn_natAbs

theorem strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0) := fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)
#align int.strict_anti_on_nat_abs Int.strictAntiOn_natAbs

theorem injOn_natAbs_Ici : InjOn natAbs (Ici 0) :=
  strictMonoOn_natAbs.injOn
#align int.inj_on_nat_abs_Ici Int.injOn_natAbs_Ici

theorem injOn_natAbs_Iic : InjOn natAbs (Iic 0) :=
  strictAntiOn_natAbs.injOn
#align int.inj_on_nat_abs_Iic Int.injOn_natAbs_Iic

end Intervals

/-! ### `toNat` -/


theorem toNat_of_nonpos : ∀ {z : ℤ}, z ≤ 0 → z.toNat = 0
  | 0, _ => rfl
  | (n + 1 : ℕ), h => (h.not_lt (by simp)).elim
  | -[n+1], _ => rfl
#align int.to_nat_of_nonpos Int.toNat_of_nonpos

/-! ### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from `Data.Int.Order`.
-/


attribute [local simp] Int.zero_div

@[simp]
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, add_comm, Int.add_mul_ediv_left, (_ : (_ / 2 : ℤ) = 0), zero_add]
  cases b
  · decide
  · show ofNat _ = _
    rw [Nat.div_eq_of_lt] <;> simp
  · decide
#align int.div2_bit Int.div2_bit

-- 2024-04-02
@[deprecated] alias le_coe_nat_sub := le_natCast_sub
@[deprecated] alias succ_coe_nat_pos := succ_natCast_pos
@[deprecated] alias coe_natAbs := natCast_natAbs
@[deprecated] alias coe_nat_eq_zero := natCast_eq_zero
@[deprecated] alias coe_nat_ne_zero := natCast_ne_zero
@[deprecated] alias coe_nat_ne_zero_iff_pos := natCast_ne_zero_iff_pos
@[deprecated] alias abs_coe_nat := abs_natCast
@[deprecated] alias coe_nat_nonpos_iff := natCast_nonpos_iff

end Int
