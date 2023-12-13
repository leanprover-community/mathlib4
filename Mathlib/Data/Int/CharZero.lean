/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Function.Support
import Mathlib.Data.Int.Cast.Field

#align_import data.int.char_zero from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/

open Nat Set

variable {α β : Type*}

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
theorem cast_div_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) :
    ((m / n : ℤ) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)
#align int.cast_div_char_zero Int.cast_div_charZero

-- Necessary for confluence with `ofNat_ediv` and `cast_div_charZero`.
@[simp, norm_cast]
theorem cast_div_ofNat_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : ℕ}
    (n_dvd : n ∣ m) : (((m : ℤ) / (n : ℤ) : ℤ) : k) = m / n := by
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd), cast_ofNat, cast_ofNat]

end Int

theorem RingHom.injective_int {α : Type*} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective
#align ring_hom.injective_int RingHom.injective_int

namespace Function
variable [AddGroupWithOne β] [CharZero β] {n : ℤ}

lemma support_int_cast (hn : n ≠ 0) : support (n : α → β) = univ :=
  support_const $ Int.cast_ne_zero.2 hn
#align function.support_int_cast Function.support_int_cast

lemma mulSupport_int_cast (hn : n ≠ 1) : mulSupport (n : α → β) = univ :=
  mulSupport_const $ Int.cast_ne_one.2 hn
#align function.mul_support_int_cast Function.mulSupport_int_cast

end Function
