/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Order.Monoid.Associated
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Order on associates of a monoid with zero

This file shows that the divisibility preorder on `Associates M` is a partial order when `M` is
cancellative that it has `0` as a top element.
-/

public section

assert_not_exists Multiset Ring

variable {M : Type*}

namespace Associates

section CommMonoidWithZero
variable [CommMonoidWithZero M] {a b c d : Associates M}

instance instOrderTop : OrderTop (Associates M) where
  top := 0
  le_top := dvd_zero

@[simp] protected lemma le_zero (a : Associates M) : a ≤ 0 := le_top

instance instBoundedOrder : BoundedOrder (Associates M) where

lemma Prime.le_or_le {p : Associates M} (hp : Prime p) (h : p ≤ a * b) : p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h

lemma dvdNotUnit_of_lt (hlt : a < b) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hlt.not_ge <| dvd_zero _
  obtain ⟨⟨x, rfl⟩, ndvd⟩ := hlt
  refine ⟨x, ?_, rfl⟩
  rintro ⟨u, rfl⟩
  simp at ndvd

end CommMonoidWithZero

section CancelCommMonoidWithZero
variable [CommMonoidWithZero M] [IsCancelMulZero M] {p a b : Associates M}

instance instPartialOrder : PartialOrder (Associates M) where
  le_antisymm := mk_surjective.forall₂.2 fun _a _b hab hba => mk_eq_mk_iff_associated.2 <|
    associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba)

lemma le_of_mul_le_mul_left (a b c : Associates M) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha <| by rwa [← mul_assoc]⟩

lemma one_or_eq_of_le_of_prime (hp : Prime p) (hap : a ≤ p) : a = 1 ∨ a = p := by
  rcases mk_surjective p with ⟨p, rfl⟩
  rcases mk_surjective a with ⟨m, rfl⟩
  simpa [mk_eq_mk_iff_associated, Associated.comm]
    using (prime_mk.1 hp).irreducible.dvd_iff.mp (mk_le_mk_iff_dvd.1 hap)

lemma dvdNotUnit_iff_lt : DvdNotUnit a b ↔ a < b := dvd_and_not_dvd_iff.symm

lemma le_one_iff : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]

instance instIsOrderedMonoid : IsOrderedMonoid (Associates M) where
  mul_le_mul_left := by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩

instance : CanonicallyOrderedMul (Associates M) where
  exists_mul_of_le h := h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩

end CancelCommMonoidWithZero
end Associates
