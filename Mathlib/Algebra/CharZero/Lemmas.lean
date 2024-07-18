/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Nat.Cast.Field

#align_import algebra.char_zero.lemmas from "leanprover-community/mathlib"@"acee671f47b8e7972a1eb6f4eed74b4b3abce829"

/-!
# Characteristic zero (additional theorems)

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main statements

* Characteristic zero implies that the additive monoid is infinite.
-/

open Function Set

namespace Nat

variable {R : Type*} [AddMonoidWithOne R] [CharZero R]

/-- `Nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def castEmbedding : ℕ ↪ R :=
  ⟨Nat.cast, cast_injective⟩
#align nat.cast_embedding Nat.castEmbedding
#align nat.cast_embedding_apply Nat.castEmbedding_apply

@[simp]
theorem cast_pow_eq_one {R : Type*} [Semiring R] [CharZero R] (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
    (q : R) ^ n = 1 ↔ q = 1 := by
  rw [← cast_pow, cast_eq_one]
  exact pow_eq_one_iff hn
#align nat.cast_pow_eq_one Nat.cast_pow_eq_one

@[simp, norm_cast]
theorem cast_div_charZero {k : Type*} [DivisionSemiring k] [CharZero k] {m n : ℕ} (n_dvd : n ∣ m) :
    ((m / n : ℕ) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  · exact cast_div n_dvd (cast_ne_zero.2 hn)
#align nat.cast_div_char_zero Nat.cast_div_charZero

end Nat

section AddMonoidWithOne
variable {α M : Type*} [AddMonoidWithOne M] [CharZero M] {n : ℕ}

instance CharZero.NeZero.two : NeZero (2 : M) :=
  ⟨by
    have : ((2 : ℕ) : M) ≠ 0 := Nat.cast_ne_zero.2 (by decide)
    rwa [Nat.cast_two] at this⟩
#align char_zero.ne_zero.two CharZero.NeZero.two

namespace Function

lemma support_natCast (hn : n ≠ 0) : support (n : α → M) = univ :=
  support_const <| Nat.cast_ne_zero.2 hn
#align function.support_nat_cast Function.support_natCast

@[deprecated (since := "2024-04-17")]
alias support_nat_cast := support_natCast

lemma mulSupport_natCast (hn : n ≠ 1) : mulSupport (n : α → M) = univ :=
  mulSupport_const <| Nat.cast_ne_one.2 hn
#align function.mul_support_nat_cast Function.mulSupport_natCast

@[deprecated (since := "2024-04-17")]
alias mulSupport_nat_cast := mulSupport_natCast

end Function
end AddMonoidWithOne

section

variable {R : Type*} [NonAssocSemiring R] [NoZeroDivisors R] [CharZero R] {a : R}

@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or_iff]
#align add_self_eq_zero add_self_eq_zero

#noalign bit0_eq_zero
#noalign zero_eq_bit0
#noalign bit0_ne_zero
#noalign zero_ne_bit0

end

section

variable {R : Type*} [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

@[simp] theorem neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero
#align neg_eq_self_iff neg_eq_self_iff

@[simp] theorem eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero
#align eq_neg_self_iff eq_neg_self_iff

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact mod_cast h
#align nat_mul_inj nat_mul_inj

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h
#align nat_mul_inj' nat_mul_inj'

#noalign bit0_injective
#noalign bit1_injective
#noalign bit0_eq_bit0
#noalign bit1_eq_bit1
#noalign bit1_eq_one
#noalign one_eq_bit1

end

section

variable {R : Type*} [DivisionSemiring R] [NeZero (2 : R)]

@[simp] lemma add_self_div_two (a : R) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel_right₀ a two_ne_zero]
#align add_self_div_two add_self_div_two
#align half_add_self add_self_div_two
@[deprecated (since := "2024-07-16")] alias half_add_self := add_self_div_two


@[simp]
theorem add_halves (a : R) : a / 2 + a / 2 = a := by rw [← add_div, add_self_div_two]
#align add_halves add_halves
#align add_halves' add_halves
@[deprecated (since := "2024-07-16")] alias add_halves' := add_halves

end
section

variable {R : Type*} [DivisionRing R] [CharZero R]

theorem sub_half (a : R) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]
#align sub_half sub_half

theorem half_sub (a : R) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]
#align half_sub half_sub

end

namespace WithTop

instance {R : Type*} [AddMonoidWithOne R] [CharZero R] :
    CharZero (WithTop R) where
  cast_injective m n h := by
    rwa [← coe_natCast, ← coe_natCast n, coe_eq_coe, Nat.cast_inj] at h

end WithTop

namespace WithBot

instance {R : Type*} [AddMonoidWithOne R] [CharZero R] :
    CharZero (WithBot R) where
  cast_injective m n h := by
    rwa [← coe_natCast, ← coe_natCast n, coe_eq_coe, Nat.cast_inj] at h

end WithBot

section RingHom

variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

theorem RingHom.charZero (ϕ : R →+* S) [CharZero S] : CharZero R :=
  ⟨fun a b h => CharZero.cast_injective (by rw [← map_natCast ϕ, ← map_natCast ϕ, h])⟩
#align ring_hom.char_zero RingHom.charZero

theorem RingHom.charZero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun hS => ϕ.charZero⟩
#align ring_hom.char_zero_iff RingHom.charZero_iff

theorem RingHom.injective_nat (f : ℕ →+* R) [CharZero R] : Function.Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective
#align ring_hom.injective_nat RingHom.injective_nat

end RingHom

section Units

variable {R : Type*} [Ring R] [CharZero R]

@[simp]
theorem units_ne_neg_self (u : Rˣ) : u ≠ -u := by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]
theorem neg_units_ne_self (u : Rˣ) : -u ≠ u := (units_ne_neg_self u).symm

end Units
