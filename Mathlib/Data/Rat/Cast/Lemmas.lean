/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity.Basic

/-!
# Some exiled lemmas about casting

These lemmas have been removed from `Mathlib/Data/Rat/Cast/Defs.lean`
to avoiding needing to import `Mathlib/Algebra/Field/Basic.lean` there.

In fact, these lemmas don't appear to be used anywhere in Mathlib,
so perhaps this file can simply be deleted.
-/

namespace Rat

variable {α : Type*} [DivisionRing α]

-- Note that this is more general than `(Rat.castHom α).map_pow`.
@[simp, norm_cast]
lemma cast_pow (p : ℚ) (n : ℕ) : ↑(p ^ n) = (p ^ n : α) := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Int.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Int.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  rcases n with - | n
  · simp
  rw [cast_def, inv_natCast_num, inv_natCast_den, if_neg n.succ_ne_zero,
    Int.sign_eq_one_of_pos (Int.ofNat_succ_pos n), Int.cast_one, one_div]

@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = (n : α)⁻¹ := by
  rcases n with n | n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, cast_neg, inv_neg, cast_inv_nat]

@[simp, norm_cast]
theorem cast_nnratCast {K} [DivisionRing K] (q : ℚ≥0) :
    ((q : ℚ) : K) = (q : K) := by
  rw [Rat.cast_def, NNRat.cast_def, NNRat.cast_def]
  have hn := @num_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  on_goal 1 => have hd := @den_div_eq_of_coprime q.num q.den ?hdp q.coprime_num_den
  case hdp => simpa only [Int.natCast_pos] using q.den_pos
  simp only [Int.cast_natCast, Nat.cast_inj] at hn hd
  rw [hn, hd, Int.cast_natCast]

/-- Casting a scientific literal via `ℚ` is the same as casting directly. -/
@[simp, norm_cast]
theorem cast_ofScientific {K} [DivisionRing K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ) = (OfScientific.ofScientific m s e : K) := by
  rw [← NNRat.cast_ofScientific (K := K), ← NNRat.cast_ofScientific, cast_nnratCast]

end Rat

namespace NNRat

@[simp, norm_cast]
theorem cast_pow {K} [DivisionSemiring K] (q : ℚ≥0) (n : ℕ) :
    NNRat.cast (q ^ n) = (NNRat.cast q : K) ^ n := by
  rw [cast_def, cast_def, den_pow, num_pow, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, ← inv_pow,
    ← (Nat.cast_commute _ _).mul_pow, ← div_eq_mul_inv]

theorem cast_zpow_of_ne_zero {K} [DivisionSemiring K] (q : ℚ≥0) (z : ℤ) (hq : (q.num : K) ≠ 0) :
    NNRat.cast (q ^ z) = (NNRat.cast q : K) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp
  · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow]
    congr
    rw [cast_inv_of_ne_zero hq]

open OfScientific in
theorem Nonneg.coe_ofScientific {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (s : Bool) (e : ℕ) :
    (ofScientific m s e : {x : K // 0 ≤ x}).val = ofScientific m s e := rfl

end NNRat
