/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.GroupPower.Lemmas

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
  -- ⊢ q ^ n = 1 ↔ q = 1
  exact pow_eq_one_iff hn
  -- 🎉 no goals
#align nat.cast_pow_eq_one Nat.cast_pow_eq_one

@[simp, norm_cast]
theorem cast_div_charZero {k : Type*} [DivisionSemiring k] [CharZero k] {m n : ℕ} (n_dvd : n ∣ m) :
    ((m / n : ℕ) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ ↑(m / 0) = ↑m / ↑0
  · simp
    -- 🎉 no goals
  · exact cast_div n_dvd (cast_ne_zero.2 hn)
    -- 🎉 no goals
#align nat.cast_div_char_zero Nat.cast_div_charZero

end Nat

section

variable (M : Type*) [AddMonoidWithOne M] [CharZero M]

instance CharZero.NeZero.two : NeZero (2 : M) :=
  ⟨by
    have : ((2 : ℕ) : M) ≠ 0 := Nat.cast_ne_zero.2 (by decide)
    -- ⊢ 2 ≠ 0
    rwa [Nat.cast_two] at this⟩
    -- 🎉 no goals
#align char_zero.ne_zero.two CharZero.NeZero.two

end

section

variable {R : Type*} [NonAssocSemiring R] [NoZeroDivisors R] [CharZero R] {a : R}

@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or_iff]
  -- 🎉 no goals
#align add_self_eq_zero add_self_eq_zero

set_option linter.deprecated false

@[simp]
theorem bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 :=
  add_self_eq_zero
#align bit0_eq_zero bit0_eq_zero

@[simp]
theorem zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 := by
  rw [eq_comm]
  -- ⊢ bit0 a = 0 ↔ a = 0
  exact bit0_eq_zero
  -- 🎉 no goals
#align zero_eq_bit0 zero_eq_bit0

theorem bit0_ne_zero : bit0 a ≠ 0 ↔ a ≠ 0 :=
  bit0_eq_zero.not
#align bit0_ne_zero bit0_ne_zero

theorem zero_ne_bit0 : 0 ≠ bit0 a ↔ a ≠ 0 :=
  zero_eq_bit0.not
#align zero_ne_bit0 zero_ne_bit0

end

section

variable {R : Type*} [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

theorem neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero
#align neg_eq_self_iff neg_eq_self_iff

theorem eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero
#align eq_neg_self_iff eq_neg_self_iff

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  -- ⊢ n = 0 ∨ a = b
  exact_mod_cast h
  -- 🎉 no goals
#align nat_mul_inj nat_mul_inj

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h
  -- 🎉 no goals
#align nat_mul_inj' nat_mul_inj'

set_option linter.deprecated false

theorem bit0_injective : Function.Injective (bit0 : R → R) := fun a b h => by
  dsimp [bit0] at h
  -- ⊢ a = b
  simp only [(two_mul a).symm, (two_mul b).symm] at h
  -- ⊢ a = b
  refine' nat_mul_inj' _ two_ne_zero
  -- ⊢ ↑2 * a = ↑2 * b
  exact_mod_cast h
  -- 🎉 no goals
#align bit0_injective bit0_injective

theorem bit1_injective : Function.Injective (bit1 : R → R) := fun a b h => by
  simp only [bit1, add_left_inj] at h
  -- ⊢ a = b
  exact bit0_injective h
  -- 🎉 no goals
#align bit1_injective bit1_injective

@[simp]
theorem bit0_eq_bit0 {a b : R} : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff
#align bit0_eq_bit0 bit0_eq_bit0

@[simp]
theorem bit1_eq_bit1 {a b : R} : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff
#align bit1_eq_bit1 bit1_eq_bit1

@[simp]
theorem bit1_eq_one {a : R} : bit1 a = 1 ↔ a = 0 := by
  rw [show (1 : R) = bit1 0 by simp, bit1_eq_bit1]
  -- 🎉 no goals
#align bit1_eq_one bit1_eq_one

@[simp]
theorem one_eq_bit1 {a : R} : 1 = bit1 a ↔ a = 0 := by
  rw [eq_comm]
  -- ⊢ bit1 a = 1 ↔ a = 0
  exact bit1_eq_one
  -- 🎉 no goals
#align one_eq_bit1 one_eq_bit1

end

section

variable {R : Type*} [DivisionRing R] [CharZero R]

@[simp]
theorem half_add_self (a : R) : (a + a) / 2 = a := by rw [← mul_two, mul_div_cancel a two_ne_zero]
                                                      -- 🎉 no goals
#align half_add_self half_add_self

@[simp]
theorem add_halves' (a : R) : a / 2 + a / 2 = a := by rw [← add_div, half_add_self]
                                                      -- 🎉 no goals
#align add_halves' add_halves'

theorem sub_half (a : R) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves']
                                                   -- 🎉 no goals
#align sub_half sub_half

theorem half_sub (a : R) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]
                                                      -- 🎉 no goals
#align half_sub half_sub

end

namespace WithTop

instance {R : Type*} [AddMonoidWithOne R] [CharZero R] :
    CharZero (WithTop R) where
  cast_injective m n h := by
    rwa [← coe_nat, ← coe_nat n, coe_eq_coe, Nat.cast_inj] at h
    -- 🎉 no goals

end WithTop

namespace WithBot

instance {R : Type*} [AddMonoidWithOne R] [CharZero R] :
    CharZero (WithBot R) where
  cast_injective m n h := by
    rwa [← coe_nat, ← coe_nat n, coe_eq_coe, Nat.cast_inj] at h
    -- 🎉 no goals

end WithBot

section RingHom

variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

theorem RingHom.charZero (ϕ : R →+* S) [hS : CharZero S] : CharZero R :=
  ⟨fun a b h => CharZero.cast_injective (by rw [← map_natCast ϕ, ← map_natCast ϕ, h])⟩
                                            -- 🎉 no goals
#align ring_hom.char_zero RingHom.charZero

theorem RingHom.charZero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
        -- ⊢ a = b
                     -- 🎉 no goals
    fun hS => ϕ.charZero⟩
#align ring_hom.char_zero_iff RingHom.charZero_iff

theorem RingHom.injective_nat (f : ℕ →+* R) [CharZero R] : Function.Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective
#align ring_hom.injective_nat RingHom.injective_nat

end RingHom
