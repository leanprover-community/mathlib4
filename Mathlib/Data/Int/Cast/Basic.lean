/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Group.Basic

#align_import data.int.cast.basic from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`).

There is also `Data.Int.Cast.Lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `Data.Int.Cast.Defs` is `Algebra.Group.Basic`.
-/


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]
                         -- 🎉 no goals
#align nat.cast_sub Nat.cast_subₓ
-- `HasLiftT` appeared in the type signature

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
               -- 🎉 no goals
  | n + 1, _ => by rw [cast_succ, add_sub_cancel]; rfl
                   -- ⊢ ↑(n + 1 - 1) = ↑n
                                                   -- 🎉 no goals
#align nat.cast_pred Nat.cast_pred

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n
#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ
-- expected `n` to be implicit, and `HasLiftT`

@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero
#align int.cast_zero Int.cast_zeroₓ
-- type had `HasLiftT`

@[simp high, nolint simpNF, norm_cast] -- this lemma competes with `Int.ofNat_eq_cast` to come later
theorem cast_ofNat (n : ℕ) : ((n : ℤ) : R) = n :=
  AddGroupWithOne.intCast_ofNat _
#align int.cast_coe_nat Int.cast_ofNatₓ
-- expected `n` to be implicit, and `HasLiftT`
#align int.cast_of_nat Int.cast_ofNatₓ

@[simp, norm_cast]
theorem int_cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℤ) : R) = OfNat.ofNat n := by
  simpa only [OfNat.ofNat] using AddGroupWithOne.intCast_ofNat (R := R) n
  -- 🎉 no goals

@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 := by
  erw [cast_ofNat, Nat.cast_one]
  -- 🎉 no goals
#align int.cast_one Int.cast_oneₓ
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
                  -- 🎉 no goals
  | (n + 1 : ℕ) => by erw [cast_ofNat, cast_negSucc]
                      -- 🎉 no goals
  | -[n+1] => by erw [cast_ofNat, cast_negSucc, neg_neg]
                 -- 🎉 no goals
#align int.cast_neg Int.cast_negₓ
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold subNatNat
  -- ⊢ ↑(match n - m with
  cases e : n - m
  · simp only [ofNat_eq_coe]
    -- ⊢ ↑↑(m - n) = ↑m - ↑n
    simp [e, Nat.le_of_sub_eq_zero e]
    -- 🎉 no goals
  · rw [cast_negSucc, Nat.add_one, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e,
      neg_sub]
#align int.cast_sub_nat_nat Int.cast_subNatNatₓ
-- type had `HasLiftT`

#align int.neg_of_nat_eq Int.negOfNat_eq

@[simp]
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [Int.cast_neg, negOfNat_eq]
                                                                  -- 🎉 no goals
#align int.cast_neg_of_nat Int.cast_negOfNat

@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.ofNat_add, Nat.cast_add]
                           -- 🎉 no goals
  | (m : ℕ), -[n+1] => by erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_add_neg]
                          -- 🎉 no goals
  | -[m+1], (n : ℕ) => by
    erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_iff_eq_add, add_assoc,
      eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] =>
    show (-[m + n + 1+1] : R) = _ by
      rw [cast_negSucc, cast_negSucc, cast_negSucc, ← neg_add_rev, ← Nat.cast_add,
        Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]
#align int.cast_add Int.cast_addₓ
-- type had `HasLiftT`

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]
  -- 🎉 no goals
#align int.cast_sub Int.cast_subₓ
-- type had `HasLiftT`

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated]
theorem ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl
#align int.coe_nat_bit0 Int.ofNat_bit0

@[norm_cast, deprecated]
theorem ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl
#align int.coe_nat_bit1 Int.ofNat_bit1

@[norm_cast, deprecated]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 (n : R) :=
  Int.cast_add _ _
#align int.cast_bit0 Int.cast_bit0

@[norm_cast, deprecated]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 (n : R) :=
  by rw [bit1, Int.cast_add, Int.cast_one, cast_bit0]; rfl
     -- ⊢ bit0 ↑n + 1 = bit1 ↑n
                                                       -- 🎉 no goals
#align int.cast_bit1 Int.cast_bit1

end deprecated

theorem cast_two : ((2 : ℤ) : R) = 2 :=
  show (((2 : ℕ) : ℤ) : R) = ((2 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
                                              -- 🎉 no goals
#align int.cast_two Int.cast_two

theorem cast_three : ((3 : ℤ) : R) = 3 :=
  show (((3 : ℕ) : ℤ) : R) = ((3 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
                                              -- 🎉 no goals
#align int.cast_three Int.cast_three

theorem cast_four : ((4 : ℤ) : R) = 4 :=
  show (((4 : ℕ) : ℤ) : R) = ((4 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
                                              -- 🎉 no goals
#align int.cast_four Int.cast_four

end Int
