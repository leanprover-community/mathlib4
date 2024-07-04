/-
Copyright (c) 2021 Yakov Peckersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Peckersky
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Fin.Basic

#align_import data.fin.basic from "leanprover-community/mathlib"@"3a2b5524a138b5d0b818b858b516d4ac8a484b03"

/-!
# Fin is a group

This file contains the additive and multiplicative monoid instances on `Fin n`.

See note [foundational algebra order theory].
-/

assert_not_exists OrderedCommMonoid
assert_not_exists MonoidWithZero

open Nat

namespace Fin
variable {m n : ℕ}

/-! ### Instances -/

instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [ext_iff, add_def, Nat.add_assoc]
  add_comm := by simp [ext_iff, add_def, Nat.add_comm]
#align fin.add_comm_semigroup Fin.addCommSemigroup

instance (n) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [ext_iff, add_def, Nat.add_assoc]
  add_comm := by simp [ext_iff, add_def, add_comm]

instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) where
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n
#align fin.add_comm_monoid Fin.addCommMonoid

instance instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  natCast n := Fin.ofNat'' n
  natCast_zero := rfl
  natCast_succ _ := ext (add_mod _ _ _)
#align fin.add_monoid_with_one Fin.instAddMonoidWithOne

instance addCommGroup (n : ℕ) [NeZero n] : AddCommGroup (Fin n) where
  __ := addCommMonoid n
  __ := neg n
  add_left_neg := fun ⟨a, ha⟩ ↦
    Fin.ext <| (Nat.mod_add_mod _ _ _).trans <| by
      rw [Fin.val_zero', Nat.sub_add_cancel, Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦
    Fin.ext <| by simp [Fin.sub_def, Fin.neg_def, Fin.add_def, Nat.add_comm]
  zsmul := zsmulRec

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instInvolutiveNeg (n : ℕ) : InvolutiveNeg (Fin n) where
  neg_neg := Nat.casesOn n finZeroElim fun _i ↦ neg_neg
#align fin.involutive_neg Fin.instInvolutiveNeg

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instIsCancelAdd (n : ℕ) : IsCancelAdd (Fin n) where
  add_left_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_right_cancel
#align fin.is_cancel_add Fin.instIsCancelAdd

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddLeftCancelSemigroup (n : ℕ) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }
#align fin.add_left_cancel_semigroup Fin.instAddLeftCancelSemigroup

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddRightCancelSemigroup (n : ℕ) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }
#align fin.add_right_cancel_semigroup Fin.instAddRightCancelSemigroup

/-! ### Miscellaneous lemmas -/

lemma coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  rw [sub_eq_add_neg, val_add_eq_ite, coe_neg_one, if_pos, Nat.add_comm, Nat.add_sub_add_left]
  conv_rhs => rw [Nat.add_comm]
  rw [Nat.add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h
#align fin.coe_sub_one Fin.coe_sub_one
#align fin.coe_sub_iff_le Fin.coe_sub_iff_le
#align fin.coe_sub_iff_lt Fin.coe_sub_iff_lt

@[simp]
lemma lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  · simp only [zero_eta, zero_sub, lt_iff_val_lt_val, val_zero, coe_neg_one, zero_lt_succ]
  have : (n + 1 + (k + 1)) % (n + 2) = k % (n + 2) := by
    rw [Nat.add_comm, Nat.add_right_comm, Nat.add_assoc, Nat.add_assoc, add_mod_right]
  simp [lt_iff_val_lt_val, ext_iff, Fin.coe_sub, this, mod_eq_of_lt ((lt_succ_self _).trans hk)]
#align fin.lt_sub_one_iff Fin.lt_sub_one_iff

@[simp] lemma le_sub_one_iff {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  simp [-val_fin_le, le_def]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, val_fin_lt, val_inj, lt_sub_one_iff, or_iff_left_iff_imp,
    eq_comm, sub_eq_iff_eq_add]
  simp
#align fin.le_sub_one_iff Fin.le_sub_one_iff

lemma sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]
#align fin.sub_one_lt_iff Fin.sub_one_lt_iff

@[simp] lemma neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

lemma neg_natCast_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp only [natCast_eq_last, neg_last]

end Fin
