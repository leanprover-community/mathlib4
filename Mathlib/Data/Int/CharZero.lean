/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Int.Cast.Lemmas

#align_import data.int.char_zero from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/

open Nat Set

variable {α β : Type*}

namespace Int

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
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd), cast_natCast, cast_natCast]

end Int

theorem RingHom.injective_int {α : Type*} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective
#align ring_hom.injective_int RingHom.injective_int

namespace Function
variable [AddGroupWithOne β] [CharZero β] {n : ℤ}

lemma support_intCast (hn : n ≠ 0) : support (n : α → β) = univ :=
  support_const <| Int.cast_ne_zero.2 hn
#align function.support_int_cast Function.support_intCast

@[deprecated (since := "2024-04-17")]
alias support_int_cast := support_intCast

lemma mulSupport_intCast (hn : n ≠ 1) : mulSupport (n : α → β) = univ :=
  mulSupport_const <| Int.cast_ne_one.2 hn
#align function.mul_support_int_cast Function.mulSupport_intCast

@[deprecated (since := "2024-04-17")]
alias mulSupport_int_cast := mulSupport_intCast

end Function
