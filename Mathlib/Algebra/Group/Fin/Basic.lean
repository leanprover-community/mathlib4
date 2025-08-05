/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Fin.Rev

/-!
# Fin is a group

This file contains the additive and multiplicative monoid instances on `Fin n`.

See note [foundational algebra order theory].
-/

assert_not_exists OrderedCommMonoid MonoidWithZero

open Nat

namespace Fin
variable {n : ℕ}

/-! ### Instances -/

instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [add_def, Nat.add_assoc]
  add_comm := by simp [add_def, Nat.add_comm]

instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) where
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  nsmul := nsmulRec
  __ := Fin.addCommSemigroup n

/--
This is not a global instance, but can introduced locally using `open Fin.NatCast in ...`.

This is not an instance because the `binop%` elaborator assumes that
there are no non-trivial coercion loops,
but this instance  would introduce a coercion from `Nat` to `Fin n` and back.
Non-trivial loops lead to undesirable and counterintuitive elaboration behavior.

For example, for `x : Fin k` and `n : Nat`,
it causes `x < n` to be elaborated as `x < ↑n` rather than `↑x < n`,
silently introducing wraparound arithmetic.
-/
def instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  natCast i := Fin.ofNat n i
  natCast_zero := rfl
  natCast_succ _ := Fin.ext (add_mod _ _ _)

namespace NatCast

attribute [scoped instance] Fin.instAddMonoidWithOne

end NatCast

instance addCommGroup (n : ℕ) [NeZero n] : AddCommGroup (Fin n) where
  __ := addCommMonoid n
  __ := neg n
  neg_add_cancel := fun ⟨a, ha⟩ ↦
    Fin.ext <| (Nat.mod_add_mod _ _ _).trans <| by
      rw [Fin.val_zero, Nat.sub_add_cancel, Nat.mod_self]
      exact le_of_lt ha
  sub := Fin.sub
  sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦
    Fin.ext <| by simp [Fin.sub_def, Fin.neg_def, Fin.add_def, Nat.add_comm]
  zsmul := zsmulRec

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instInvolutiveNeg (n : ℕ) : InvolutiveNeg (Fin n) where
  neg_neg := Nat.casesOn n finZeroElim fun _i ↦ neg_neg

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instIsCancelAdd (n : ℕ) : IsCancelAdd (Fin n) where
  add_left_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ ↦ add_right_cancel

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddLeftCancelSemigroup (n : ℕ) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddRightCancelSemigroup (n : ℕ) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-! ### Miscellaneous lemmas -/

open scoped Fin.NatCast Fin.IntCast in
/-- Variant of `Fin.intCast_def` with `Nat.cast` on the RHS. -/
theorem intCast_def' {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then ↑x.natAbs else -↑x.natAbs :=
  Fin.intCast_def _

lemma coe_sub_one (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  rw [sub_eq_add_neg, val_add_eq_ite, coe_neg_one, if_pos, Nat.add_comm, Nat.add_sub_add_left]
  conv_rhs => rw [Nat.add_comm]
  rw [Nat.add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h

@[simp]
lemma lt_sub_iff {n : ℕ} {a b : Fin n} : a < a - b ↔ a < b := by
  rcases n with - | n
  · exact a.elim0
  constructor
  · contrapose!
    intro h
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (Fin.not_lt.mp h)
    simpa only [Fin.not_lt, le_iff_val_le_val, sub_def, hl, ← Nat.add_assoc, Nat.add_mod_left,
      Nat.mod_eq_of_lt, Nat.sub_add_cancel b.is_lt.le] using
        (le_trans (mod_le _ _) (le_add_left _ _))
  · intro h
    rw [lt_iff_val_lt_val, sub_def]
    simp only
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt b.is_lt
    have : n + 1 - b = k + 1 := by
      simp_rw [hk, Nat.add_assoc, Nat.add_sub_cancel_left]
      -- simp_rw because, otherwise, rw tries to rewrite inside `b : Fin (n + 1)`
    rw [this, Nat.mod_eq_of_lt (hk.ge.trans_lt' ?_), Nat.lt_add_left_iff_pos] <;>
    omega

@[simp]
lemma sub_le_iff {n : ℕ} {a b : Fin n} : a - b ≤ a ↔ b ≤ a := by
  rw [← not_iff_not, Fin.not_le, Fin.not_le, lt_sub_iff]

@[simp]
lemma lt_one_iff {n : ℕ} (x : Fin (n + 2)) : x < 1 ↔ x = 0 := by
  simp [lt_iff_val_lt_val]

lemma lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  simp

@[simp] lemma le_sub_one_iff {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
  simp only [le_def]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, val_fin_lt, val_inj, lt_sub_one_iff, or_iff_left_iff_imp,
    eq_comm, sub_eq_iff_eq_add]
  simp

lemma sub_one_lt_iff {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [lt_def, not_lt, val_fin_le, le_sub_one_iff, le_zero_iff]

@[simp] lemma neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

open Fin.NatCast in
lemma neg_natCast_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp only [natCast_eq_last, neg_last]

lemma rev_add (a b : Fin n) : rev (a + b) = rev a - b := by
  cases n
  · exact a.elim0
  rw [← last_sub, ← last_sub, sub_add_eq_sub_sub]

lemma rev_sub (a b : Fin n) : rev (a - b) = rev a + b := by
  rw [rev_eq_iff, rev_add, rev_rev]

lemma add_lt_left_iff {n : ℕ} {a b : Fin n} : a + b < a ↔ rev b < a := by
  rw [← rev_lt_rev, Iff.comm, ← rev_lt_rev, rev_add, lt_sub_iff, rev_rev]

end Fin
