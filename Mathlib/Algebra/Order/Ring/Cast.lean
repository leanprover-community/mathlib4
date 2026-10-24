/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Order properties of cast of integers

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Mathlib/Data/Int/Cast/Basic.lean`.

## TODO

Move order lemmas about `Nat.cast`, `Rat.cast`, `NNRat.cast` here.
-/

public section

open Nat

variable {R : Type*}

namespace Int
section OrderedAddGroupWithOne

variable [AddGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]

@[gcongr]
lemma cast_mono : Monotone (Int.cast : ℤ → R) := by
  intro m n h
  rw [← sub_nonneg] at h
  rw [← add_sub_cancel m n, cast_add, le_add_iff_nonneg_right]
  lift n - m to ℕ using h with k hk
  simp

@[simp] lemma cast_nonneg : ∀ {n : ℤ}, 0 ≤ n → (0 : R) ≤ n | (n : ℕ), _ => by simp

variable [NeZero (1 : R)] {m n : ℤ}

@[simp] lemma cast_nonneg_iff : ∀ {n : ℤ}, (0 : R) ≤ n ↔ 0 ≤ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    have : -(n : R) < 1 := lt_of_le_of_lt (by simp) zero_lt_one
    simpa using not_le_of_gt this

@[simp, norm_cast] lemma cast_le : (m : R) ≤ n ↔ m ≤ n := by
  rw [← add_sub_cancel m n, cast_add]
  simp [-cast_sub]

lemma cast_strictMono : StrictMono (fun x : ℤ => (x : R)) :=
  strictMono_of_le_iff_le fun _ _ => cast_le.symm

@[simp, norm_cast, gcongr] lemma cast_lt : (m : R) < n ↔ m < n := cast_strictMono.lt_iff_lt

@[simp] lemma cast_nonpos : (n : R) ≤ 0 ↔ n ≤ 0 := by rw [← cast_zero, cast_le]

@[simp] lemma cast_pos : (0 : R) < n ↔ 0 < n := by rw [← cast_zero, cast_lt]

@[simp] lemma cast_lt_zero : (n : R) < 0 ↔ n < 0 := by rw [← cast_zero, cast_lt]

end OrderedAddGroupWithOne

section LinearOrderedAddGroupWithOne

variable [AddGroupWithOne R] [LinearOrder R] [AddLeftMono R] [ZeroLEOneClass R]
variable {a b n : ℤ}

@[simp, norm_cast]
lemma cast_min : ↑(min a b) = (min a b : R) := Monotone.map_min cast_mono

@[simp, norm_cast]
lemma cast_max : (↑(max a b) : R) = max (a : R) (b : R) := Monotone.map_max cast_mono

@[simp, norm_cast]
lemma cast_abs : (↑|a| : R) = |(a : R)| := by simp [abs_eq_max_neg]

lemma cast_one_le_of_pos (h : 0 < a) : (1 : R) ≤ a := by
  simpa using Int.cast_mono (Int.add_one_le_of_lt h)

lemma cast_le_neg_one_of_neg (h : a < 0) : (a : R) ≤ -1 := by
  simpa using Int.cast_mono (Int.le_sub_one_of_lt h)

variable (R) in
lemma cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n ≠ 0) : (n : R) ≤ -1 ∨ 1 ≤ (n : R) :=
  hn.lt_or_gt.imp cast_le_neg_one_of_neg cast_one_le_of_pos

end LinearOrderedAddGroupWithOne

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] {x : R}

lemma nonneg_mul_add_sq_of_abs_le_one (n : ℤ) (hx : |x| ≤ 1) : (0 : R) ≤ n * x + n * n := by
  wlog hn : n ≥ 0 generalizing x n
  · simpa using this (x := -x) (-n) (by simpa only [abs_neg] using hx)
      (Int.neg_nonneg.mpr (Int.le_of_not_le hn))
  lift n to ℕ using hn
  rw [cast_natCast, ← mul_add, ← nsmul_eq_mul]
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [zero_nsmul]
  · refine nsmul_nonneg ?_ n
    simpa using add_le_add (neg_le_of_abs_le hx) (Nat.mono_cast hn)

@[deprecated (since := "2026-09-17")]
alias nneg_mul_add_sq_of_abs_le_one := nonneg_mul_add_sq_of_abs_le_one

end LinearOrderedRing
end Int
