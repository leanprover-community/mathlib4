/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.int.char_zero
! leanprover-community/mathlib commit 29cb56a7b35f72758b05a30490e1f10bd62c35c1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Int.Cast.Field

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/


variable {α : Type _}

open Nat

namespace Int

@[simp]
theorem cast_eq_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
  ⟨fun h => by
    cases n
    · erw [Int.cast_ofNat] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction,
    fun h => by rw [h, cast_zero]⟩
#align int.cast_eq_zero Int.cast_eq_zero

@[simp, norm_cast]
theorem cast_inj [AddGroupWithOne α] [CharZero α] {m n : ℤ} : (m : α) = n ↔ m = n := by
  rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]
#align int.cast_inj Int.cast_inj

theorem cast_injective [AddGroupWithOne α] [CharZero α] : Function.Injective (Int.cast : ℤ → α)
  | _, _ => cast_inj.1
#align int.cast_injective Int.cast_injective

theorem cast_ne_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align int.cast_ne_zero Int.cast_ne_zero

@[simp]
theorem cast_eq_one [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) = 1 ↔ n = 1 := by
  rw [← cast_one, cast_inj]
#align int.cast_eq_one Int.cast_eq_one

theorem cast_ne_one [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.not
#align int.cast_ne_one Int.cast_ne_one

@[simp, norm_cast]
theorem cast_div_charZero {k : Type _} [DivisionRing k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) :
    ((m / n : ℤ) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)
#align int.cast_div_char_zero Int.cast_div_charZero

end Int

theorem RingHom.injective_int {α : Type _} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective
#align ring_hom.injective_int RingHom.injective_int
