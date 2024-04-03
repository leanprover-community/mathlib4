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
assumptions I (DT) am not convinced are necessary. If that turns out to be true, they could be moved to `Algebra.Group.Even`

## See also

`Algebra.Group.Even` for the definition of even elements.
-/

assert_not_exists OrderedRing

open MulOpposite

variable {F α β R : Type*}

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ} {a : α}

@[simp]
theorem Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
#align even.neg_pow Even.neg_pow

theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]
#align even.neg_one_pow Even.neg_one_pow

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  exact zpow_bit0_neg _ _
#align even.neg_zpow Even.neg_zpow

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

section Semiring

variable [Semiring α] [Semiring β] {m n : α}

theorem even_iff_exists_two_mul (m : α) : Even m ↔ ∃ c, m = 2 * c := by
  simp [even_iff_exists_two_nsmul]
#align even_iff_exists_two_mul even_iff_exists_two_mul

theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]
#align even_iff_two_dvd even_iff_two_dvd

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd
#align even.two_dvd Even.two_dvd

theorem Even.trans_dvd (hm : Even m) (hn : m ∣ n) : Even n :=
  even_iff_two_dvd.2 <| hm.two_dvd.trans hn
#align even.trans_dvd Even.trans_dvd

theorem Dvd.dvd.even (hn : m ∣ n) (hm : Even m) : Even n :=
  hm.trans_dvd hn
#align has_dvd.dvd.even Dvd.dvd.even

@[simp]
theorem range_two_mul (α) [Semiring α] : (Set.range fun x : α => 2 * x) = { a | Even a } := by
  ext x
  simp [eq_comm, two_mul, Even]
#align range_two_mul range_two_mul

set_option linter.deprecated false in
@[simp] theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩
#align even_bit0 even_bit0

@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, by rw [one_add_one_eq_two]⟩
#align even_two even_two

@[simp]
theorem Even.mul_left (hm : Even m) (n) : Even (n * m) :=
  hm.map (AddMonoidHom.mulLeft n)
#align even.mul_left Even.mul_left

@[simp]
theorem Even.mul_right (hm : Even m) (n) : Even (m * n) :=
  hm.map (AddMonoidHom.mulRight n)
#align even.mul_right Even.mul_right

theorem even_two_mul (m : α) : Even (2 * m) :=
  ⟨m, two_mul _⟩
#align even_two_mul even_two_mul

theorem Even.pow_of_ne_zero (hm : Even m) : ∀ {a : ℕ}, a ≠ 0 → Even (m ^ a)
  | 0, a0 => (a0 rfl).elim
  | a + 1, _ => by
    rw [pow_succ]
    exact hm.mul_left _
#align even.pow_of_ne_zero Even.pow_of_ne_zero

section WithOdd

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1
#align odd Odd

set_option linter.deprecated false in
theorem odd_iff_exists_bit1 {a : α} : Odd a ↔ ∃ b, a = bit1 b :=
  exists_congr fun b => by
    rw [two_mul]
    rfl
#align odd_iff_exists_bit1 odd_iff_exists_bit1

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1
#align odd.exists_bit1 Odd.exists_bit1

set_option linter.deprecated false in
@[simp] theorem odd_bit1 (a : α) : Odd (bit1 a) :=
  odd_iff_exists_bit1.2 ⟨a, rfl⟩
#align odd_bit1 odd_bit1

@[simp]
theorem range_two_mul_add_one (α : Type*) [Semiring α] :
    (Set.range fun x : α => 2 * x + 1) = { a | Odd a } := by
  ext x
  simp [Odd, eq_comm]
#align range_two_mul_add_one range_two_mul_add_one

theorem Even.add_odd : Even m → Odd n → Odd (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩
#align even.add_odd Even.add_odd

theorem Even.odd_add : Even m → Odd n → Odd (n + m) :=
  fun he ho ↦ by simp only [he.add_odd ho, add_comm n m]

theorem Odd.add_even (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  rw [add_comm]
  exact hn.add_odd hm
#align odd.add_even Odd.add_even

theorem Odd.add_odd : Odd m → Odd n → Even (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨n + m + 1, _⟩
  rw [two_mul, two_mul]
  ac_rfl
#align odd.add_odd Odd.add_odd

@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one

@[simp] lemma Even.add_one (h : Even m) : Odd (m + 1) := h.add_odd odd_one

@[simp] lemma Even.one_add (h : Even m) : Odd (1 + m) := h.odd_add odd_one

theorem odd_two_mul_add_one (m : α) : Odd (2 * m + 1) :=
  ⟨m, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

@[simp] lemma odd_add_self_one' : Odd (m + (m + 1)) := by simp [← add_assoc]

@[simp] lemma odd_add_one_self : Odd (m + 1 + m) := by simp [add_comm _ m]

@[simp] lemma odd_add_one_self' : Odd (m + (1 + m)) := by simp [add_comm 1 m]

@[simp] lemma one_add_self_self : Odd (1 + m + m) := by simp [add_comm 1 m]

theorem Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd m → Odd (f m) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp [two_mul]⟩
#align odd.map Odd.map

@[simp]
theorem Odd.mul : Odd m → Odd n → Odd (m * n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨2 * m * n + n + m, _⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

theorem Odd.pow (hm : Odd m) : ∀ {a : ℕ}, Odd (m ^ a)
  | 0 => by
    rw [pow_zero]
    exact odd_one
  | a + 1 => by
    rw [pow_succ]
    exact (Odd.pow hm).mul hm
#align odd.pow Odd.pow

end WithOdd

end Semiring

section Monoid

variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}

theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
#align odd.neg_pow Odd.neg_pow

@[simp]
theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section Ring

variable [Ring α] {a b : α} {n : ℕ}

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [even_neg, even_two]
-/
-- @[simp]
theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
#align even_neg_two even_neg_two

theorem Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right, ←
    neg_add, hk]
#align odd.neg Odd.neg

@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [odd_neg, odd_one]
-/
-- @[simp]
theorem odd_neg_one : Odd (-1 : α) := by simp
#align odd_neg_one odd_neg_one

theorem Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_even hb.neg
#align odd.sub_even Odd.sub_even

theorem Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align even.sub_odd Even.sub_odd

theorem Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align odd.sub_odd Odd.sub_odd

end Ring
