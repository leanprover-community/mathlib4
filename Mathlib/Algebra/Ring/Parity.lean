/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Set.Defs

#align_import algebra.parity from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Even and odd elements in rings

This file defines odd elements and proves some general facts about even and odd elements of rings.

As opposed to `Even`, `Odd` does not have a multiplicative counterpart.

## TODO

Try to generalize `Even` lemmas further. For example, there are still a few lemmas whose `Semiring`
assumptions I (DT) am not convinced are necessary. If that turns out to be true, they could be moved
to `Algebra.Group.Even`.

## See also

`Algebra.Group.Even` for the definition of even elements.
-/

assert_not_exists OrderedRing

open MulOpposite

variable {F α β R : Type*}

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ} {a : α}

@[simp] lemma Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
#align even.neg_pow Even.neg_pow

lemma Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]
#align even.neg_one_pow Even.neg_one_pow

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

lemma Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a; exact zpow_bit0_neg _ _
#align even.neg_zpow Even.neg_zpow

lemma Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

@[simp] lemma isSquare_zero [MulZeroClass α] : IsSquare (0 : α) := ⟨0, (mul_zero _).symm⟩
#align is_square_zero isSquare_zero

section Semiring
variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

lemma even_iff_exists_two_mul : Even a ↔ ∃ b, a = 2 * b := by simp [even_iff_exists_two_nsmul]
#align even_iff_exists_two_mul even_iff_exists_two_mul

lemma even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]
#align even_iff_two_dvd even_iff_two_dvd

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd
#align even.two_dvd Even.two_dvd

lemma Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b :=
  even_iff_two_dvd.2 <| ha.two_dvd.trans hab
#align even.trans_dvd Even.trans_dvd

lemma Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b := ha.trans_dvd hab
#align has_dvd.dvd.even Dvd.dvd.even

@[simp] lemma range_two_mul (α) [Semiring α] : Set.range (fun x : α ↦ 2 * x) = {a | Even a} := by
  ext x
  simp [eq_comm, two_mul, Even]
#align range_two_mul range_two_mul

set_option linter.deprecated false in
@[simp] lemma even_bit0 (a : α) : Even (bit0 a) := ⟨a, rfl⟩
#align even_bit0 even_bit0

@[simp] lemma even_two : Even (2 : α) := ⟨1, by rw [one_add_one_eq_two]⟩
#align even_two even_two

@[simp] lemma Even.mul_left (ha : Even a) (b) : Even (b * a) := ha.map (AddMonoidHom.mulLeft _)
#align even.mul_left Even.mul_left

@[simp] lemma Even.mul_right (ha : Even a) (b) : Even (a * b) := ha.map (AddMonoidHom.mulRight _)
#align even.mul_right Even.mul_right

lemma even_two_mul (a : α) : Even (2 * a) := ⟨a, two_mul _⟩
#align even_two_mul even_two_mul

lemma Even.pow_of_ne_zero (ha : Even a) : ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
  | n + 1, _ => by rw [pow_succ]; exact ha.mul_left _
#align even.pow_of_ne_zero Even.pow_of_ne_zero

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop := ∃ k, a = 2 * k + 1
#align odd Odd

set_option linter.deprecated false in
lemma odd_iff_exists_bit1 : Odd a ↔ ∃ b, a = bit1 b := exists_congr fun b ↦ by rw [two_mul]; rfl
#align odd_iff_exists_bit1 odd_iff_exists_bit1

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1
#align odd.exists_bit1 Odd.exists_bit1

set_option linter.deprecated false in
@[simp] lemma odd_bit1 (a : α) : Odd (bit1 a) := odd_iff_exists_bit1.2 ⟨a, rfl⟩
#align odd_bit1 odd_bit1

@[simp] lemma range_two_mul_add_one (α : Type*) [Semiring α] :
    Set.range (fun x : α ↦ 2 * x + 1) = {a | Odd a} := by ext x; simp [Odd, eq_comm]
#align range_two_mul_add_one range_two_mul_add_one

lemma Even.add_odd : Even a → Odd b → Odd (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩
#align even.add_odd Even.add_odd

lemma Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a) := add_comm a b ▸ ha.add_odd hb
lemma Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := add_comm a b ▸ hb.add_odd ha
#align odd.add_even Odd.add_even

lemma Odd.add_odd : Odd a → Odd b → Even (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine' ⟨a + b + 1, _⟩
  rw [two_mul, two_mul]
  ac_rfl
#align odd.add_odd Odd.add_odd

@[simp] lemma odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one

@[simp] lemma Even.add_one (h : Even a) : Odd (a + 1) := h.add_odd odd_one
@[simp] lemma Even.one_add (h : Even a) : Odd (1 + a) := h.odd_add odd_one

lemma odd_two_mul_add_one (a : α) : Odd (2 * a + 1) := ⟨_, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

@[simp] lemma odd_add_self_one' : Odd (a + (a + 1)) := by simp [← add_assoc]
@[simp] lemma odd_add_one_self : Odd (a + 1 + a) := by simp [add_comm _ a]
@[simp] lemma odd_add_one_self' : Odd (a + (1 + a)) := by simp [add_comm 1 a]

lemma Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩
#align odd.map Odd.map

@[simp] lemma Odd.mul : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine' ⟨2 * a * b + b + a, _⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

lemma Odd.pow (ha : Odd a) : ∀ {n : ℕ}, Odd (a ^ n)
  | 0 => by
    rw [pow_zero]
    exact odd_one
  | n + 1 => by rw [pow_succ]; exact ha.pow.mul ha
#align odd.pow Odd.pow

lemma Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction' k with k ih
  · simpa
  have : a ^ 2 = b ^ 2 := add_right_cancel $
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul, ← pow_add, add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]

end Semiring

section Monoid
variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}

lemma Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
#align odd.neg_pow Odd.neg_pow

@[simp] lemma Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section Ring
variable [Ring α] {a b : α} {n : ℕ}

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [even_neg, even_two]
-/
-- @[simp]
lemma even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
#align even_neg_two even_neg_two

lemma Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right,
    ← neg_add, hk]
#align odd.neg Odd.neg

@[simp] lemma odd_neg : Odd (-a) ↔ Odd a := ⟨fun h ↦ neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [odd_neg, odd_one]
-/
-- @[simp]
lemma odd_neg_one : Odd (-1 : α) := by simp
#align odd_neg_one odd_neg_one

lemma Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg
#align odd.sub_even Odd.sub_even

lemma Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg
#align even.sub_odd Even.sub_odd

lemma Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg
#align odd.sub_odd Odd.sub_odd

end Ring
