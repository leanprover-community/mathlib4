/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Ring.Units
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Characteristic zero rings
-/

assert_not_exists Field

open Function Set

variable {α R S : Type*} {n : ℕ}

section AddMonoidWithOne
variable [AddMonoidWithOne R] [CharZero R]

/-- `Nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def Nat.castEmbedding : ℕ ↪ R := ⟨Nat.cast, cast_injective⟩

instance CharZero.NeZero.two : NeZero (2 : R) where
  out := by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

namespace Function

lemma support_natCast (hn : n ≠ 0) : support (n : α → R) = univ :=
  support_const <| Nat.cast_ne_zero.2 hn

lemma mulSupport_natCast (hn : n ≠ 1) : mulSupport (n : α → R) = univ :=
  mulSupport_const <| Nat.cast_ne_one.2 hn

end Function
end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R] [NonAssocSemiring S]

namespace RingHom

lemma charZero (ϕ : R →+* S) [CharZero S] : CharZero R where
  cast_injective a b h := CharZero.cast_injective (R := S) <| by
    rw [← map_natCast ϕ, ← map_natCast ϕ, h]

lemma charZero_iff {ϕ : R →+* S} (hϕ : Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩

lemma injective_nat (f : ℕ →+* R) [CharZero R] : Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

end RingHom

variable [NoZeroDivisors R] [CharZero R] {a : R}

@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

end NonAssocSemiring

section Semiring
variable [Semiring R] [CharZero R]

@[simp] lemma Nat.cast_pow_eq_one {a : ℕ} (hn : n ≠ 0) : (a : R) ^ n = 1 ↔ a = 1 := by
  simp [← cast_pow, cast_eq_one, hn]

end Semiring

section NonAssocRing
variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

@[scoped simp] theorem CharZero.neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero

@[scoped simp] theorem CharZero.eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact mod_cast h

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h

end NonAssocRing

section Ring
variable [Ring R] [CharZero R]

@[simp]
theorem units_ne_neg_self (u : Rˣ) : u ≠ -u := by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]
theorem neg_units_ne_self (u : Rˣ) : -u ≠ u := (units_ne_neg_self u).symm

end Ring
