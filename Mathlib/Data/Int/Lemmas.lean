/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Set.Function
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Int.Bitwise
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Order.Lemmas

#align_import data.int.lemmas from "leanprover-community/mathlib"@"09597669f02422ed388036273d8848119699c22f"

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`Data.Int.Basic` or `Data.Int.Order`.

-/


open Nat

namespace Int

theorem le_coe_nat_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) := by
  by_cases h : m ≥ n
  -- ⊢ ↑m - ↑n ≤ ↑(m - n)
  · exact le_of_eq (Int.ofNat_sub h).symm
    -- 🎉 no goals
  · simp [le_of_not_ge h, ofNat_le]
    -- 🎉 no goals
#align int.le_coe_nat_sub Int.le_coe_nat_sub

/-! ### `succ` and `pred` -/


-- Porting note: simp can prove this @[simp]
theorem succ_coe_nat_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)
                         -- 🎉 no goals
#align int.succ_coe_nat_pos Int.succ_coe_nat_pos

/-! ### `natAbs` -/


variable {a b : ℤ} {n : ℕ}

theorem natAbs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq, sq]
  -- ⊢ natAbs a = natAbs b ↔ a * a = b * b
  exact natAbs_eq_iff_mul_self_eq
  -- 🎉 no goals
#align int.nat_abs_eq_iff_sq_eq Int.natAbs_eq_iff_sq_eq

theorem natAbs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq, sq]
  -- ⊢ natAbs a < natAbs b ↔ a * a < b * b
  exact natAbs_lt_iff_mul_self_lt
  -- 🎉 no goals
#align int.nat_abs_lt_iff_sq_lt Int.natAbs_lt_iff_sq_lt

theorem natAbs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  -- ⊢ natAbs a ≤ natAbs b ↔ a * a ≤ b * b
  exact natAbs_le_iff_mul_self_le
  -- 🎉 no goals
#align int.nat_abs_le_iff_sq_le Int.natAbs_le_iff_sq_le

theorem natAbs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq ha hb, ← natAbs_eq_iff_sq_eq]
                                      -- 🎉 no goals
#align int.nat_abs_inj_of_nonneg_of_nonneg Int.natAbs_inj_of_nonneg_of_nonneg

theorem natAbs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)
#align int.nat_abs_inj_of_nonpos_of_nonpos Int.natAbs_inj_of_nonpos_of_nonpos

theorem natAbs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)
  -- 🎉 no goals
#align int.nat_abs_inj_of_nonneg_of_nonpos Int.natAbs_inj_of_nonneg_of_nonpos

theorem natAbs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb
  -- 🎉 no goals
#align int.nat_abs_inj_of_nonpos_of_nonneg Int.natAbs_inj_of_nonpos_of_nonneg

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
                                    -- 🎉 no goals
  | -[n+1], _ => rfl
#align int.to_nat_of_nonpos Int.toNat_of_nonpos

/-! ### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from `Data.Int.Order`.
-/


attribute [local simp] Int.zero_div

@[simp]
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, add_comm, Int.add_mul_ediv_left, (_ : (_ / 2 : ℤ) = 0), zero_add]
  -- ⊢ (bif b then 1 else 0) / 2 = 0
  cases b
  · simp
    -- 🎉 no goals
  · show ofNat _ = _
    -- ⊢ ofNat (1 / 2) = 0
    rw [Nat.div_eq_zero] <;> simp
    -- ⊢ ofNat 0 = 0
                             -- 🎉 no goals
                             -- 🎉 no goals
  · decide
    -- 🎉 no goals
#align int.div2_bit Int.div2_bit

end Int
