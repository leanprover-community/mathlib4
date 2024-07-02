/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order

#align_import data.int.cast.lemmas from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Order properties of cast of integers

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Mathlib.Data.Int.Cast.Basic`.

## TODO

Move order lemmas about `Nat.cast`, `Rat.cast`, `NNRat.cast` here.
-/

open Function Nat

variable {R : Type*}

namespace Int
section OrderedRing
variable [OrderedRing R]

lemma cast_mono : Monotone (Int.cast : ℤ → R) := by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to ℕ using h with k hk
  rw [← sub_nonneg, ← cast_sub, ← hk, cast_natCast]
  exact k.cast_nonneg
#align int.cast_mono Int.cast_mono

variable [Nontrivial R] {m n : ℤ}

@[simp] lemma cast_nonneg : ∀ {n : ℤ}, (0 : R) ≤ n ↔ 0 ≤ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    have : -(n : R) < 1 := lt_of_le_of_lt (by simp) zero_lt_one
    simpa [(negSucc_lt_zero n).not_le, ← sub_eq_add_neg, le_neg] using this.not_le
#align int.cast_nonneg Int.cast_nonneg

@[simp, norm_cast] lemma cast_le : (m : R) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]
#align int.cast_le Int.cast_le

lemma cast_strictMono : StrictMono (fun x : ℤ => (x : R)) :=
  strictMono_of_le_iff_le fun _ _ => cast_le.symm
#align int.cast_strict_mono Int.cast_strictMono

@[simp, norm_cast] lemma cast_lt : (m : R) < n ↔ m < n := cast_strictMono.lt_iff_lt
#align int.cast_lt Int.cast_lt

@[simp] lemma cast_nonpos : (n : R) ≤ 0 ↔ n ≤ 0 := by rw [← cast_zero, cast_le]
#align int.cast_nonpos Int.cast_nonpos

@[simp] lemma cast_pos : (0 : R) < n ↔ 0 < n := by rw [← cast_zero, cast_lt]
#align int.cast_pos Int.cast_pos

@[simp] lemma cast_lt_zero : (n : R) < 0 ↔ n < 0 := by rw [← cast_zero, cast_lt]
#align int.cast_lt_zero Int.cast_lt_zero

end OrderedRing

section LinearOrderedRing
variable [LinearOrderedRing R] {a b n : ℤ} {x : R}

@[simp, norm_cast]
lemma cast_min : ↑(min a b) = (min a b : R) := Monotone.map_min cast_mono
#align int.cast_min Int.cast_min

@[simp, norm_cast]
lemma cast_max : (↑(max a b) : R) = max (a : R) (b : R) := Monotone.map_max cast_mono
#align int.cast_max Int.cast_max

@[simp, norm_cast]
lemma cast_abs : (↑|a| : R) = |(a : R)| := by simp [abs_eq_max_neg]
#align int.cast_abs Int.cast_abs

lemma cast_one_le_of_pos (h : 0 < a) : (1 : R) ≤ a := mod_cast Int.add_one_le_of_lt h
#align int.cast_one_le_of_pos Int.cast_one_le_of_pos

lemma cast_le_neg_one_of_neg (h : a < 0) : (a : R) ≤ -1 := by
  rw [← Int.cast_one, ← Int.cast_neg, cast_le]
  exact Int.le_sub_one_of_lt h
#align int.cast_le_neg_one_of_neg Int.cast_le_neg_one_of_neg

variable (R) in
lemma cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n ≠ 0) : (n : R) ≤ -1 ∨ 1 ≤ (n : R) :=
  hn.lt_or_lt.imp cast_le_neg_one_of_neg cast_one_le_of_pos
#align int.cast_le_neg_one_or_one_le_cast_of_ne_zero Int.cast_le_neg_one_or_one_le_cast_of_ne_zero

lemma nneg_mul_add_sq_of_abs_le_one (n : ℤ) (hx : |x| ≤ 1) : (0 : R) ≤ n * x + n * n := by
  have hnx : 0 < n → 0 ≤ x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rwa [add_left_neg] at this
  have hnx' : n < 0 → x + n ≤ 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rwa [add_right_neg] at this
  rw [← mul_add, mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨mod_cast h.le, hnx h⟩
#align int.nneg_mul_add_sq_of_abs_le_one Int.nneg_mul_add_sq_of_abs_le_one

lemma cast_natAbs : (n.natAbs : R) = |n| := by
  cases n
  · simp
  · rw [abs_eq_natAbs, natAbs_negSucc, cast_succ, cast_natCast, cast_succ]
#align int.cast_nat_abs Int.cast_natAbs

end LinearOrderedRing
end Int

/-! ### Order dual -/

open OrderDual

namespace OrderDual

instance instIntCast             [IntCast R]             : IntCast Rᵒᵈ             := ‹_›
instance instAddGroupWithOne     [AddGroupWithOne R]     : AddGroupWithOne Rᵒᵈ     := ‹_›
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵒᵈ := ‹_›

end OrderDual

@[simp] lemma toDual_intCast [IntCast R] (n : ℤ) : toDual (n : R) = n := rfl
#align to_dual_int_cast toDual_intCast

@[simp] lemma ofDual_intCast [IntCast R] (n : ℤ) : (ofDual n : R) = n := rfl
#align of_dual_int_cast ofDual_intCast

/-! ### Lexicographic order -/

namespace Lex

instance instIntCast             [IntCast R]             : IntCast (Lex R)             := ‹_›
instance instAddGroupWithOne     [AddGroupWithOne R]     : AddGroupWithOne (Lex R)     := ‹_›
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne (Lex R) := ‹_›

end Lex

@[simp] lemma toLex_intCast [IntCast R] (n : ℤ) : toLex (n : R) = n := rfl
#align to_lex_int_cast toLex_intCast

@[simp] lemma ofLex_intCast [IntCast R] (n : ℤ) : (ofLex n : R) = n := rfl
#align of_lex_int_cast ofLex_intCast
