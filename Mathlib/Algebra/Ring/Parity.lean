/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Set.Basic

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
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]
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
  refine ⟨a + b + 1, ?_⟩
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

#noalign one_add_self_self

lemma Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩
#align odd.map Odd.map

@[simp] lemma Odd.mul : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
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

namespace Nat
variable {m n : ℕ}

lemma odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ ↦ by omega, fun h ↦ ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩⟩
#align nat.odd_iff Nat.odd_iff

instance : DecidablePred (Odd : ℕ → Prop) := fun _ ↦ decidable_of_iff _ odd_iff.symm

lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, mod_two_ne_one]
#align nat.not_odd_iff Nat.not_odd_iff

lemma even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]
#align nat.even_iff_not_odd Nat.even_iff_not_odd

@[simp] lemma odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]
#align nat.odd_iff_not_even Nat.odd_iff_not_even

lemma _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by
  rwa [← even_iff_two_dvd, ← odd_iff_not_even]

lemma isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, odd_iff_not_even]
#align nat.is_compl_even_odd Nat.isCompl_even_odd

lemma even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) := by
  simp [Xor', odd_iff_not_even, Decidable.em (Even n)]
#align nat.even_xor_odd Nat.even_xor_odd

lemma even_or_odd (n : ℕ) : Even n ∨ Odd n := (even_xor_odd n).or
#align nat.even_or_odd Nat.even_or_odd

lemma even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n
#align nat.even_or_odd' Nat.even_or_odd'

lemma even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;> use k
  · simpa only [← two_mul, eq_self_iff_true, xor_true] using (succ_ne_self (2 * k)).symm
  · simpa only [xor_true, xor_comm] using (succ_ne_self _)
#align nat.even_xor_odd' Nat.even_xor_odd'

lemma mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 :=
  ((even_or_odd m).elim fun hm ↦ by rw [even_iff.1 hm, odd_iff.1 (hm.add_odd hn)]) fun hm ↦ by
    rw [odd_iff.1 hm, even_iff.1 (hm.add_odd hn)]
#align nat.mod_two_add_add_odd_mod_two Nat.mod_two_add_add_odd_mod_two

@[simp] lemma mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 :=
  mod_two_add_add_odd_mod_two m odd_one
#align nat.mod_two_add_succ_mod_two Nat.mod_two_add_succ_mod_two

@[simp] lemma succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 := by
  rw [add_comm, mod_two_add_succ_mod_two]
#align nat.succ_mod_two_add_mod_two Nat.succ_mod_two_add_mod_two

lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align nat.even_add' Nat.even_add'

set_option linter.deprecated false in
@[simp] lemma not_even_bit1 (n : ℕ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]
#align nat.not_even_bit1 Nat.not_even_bit1

lemma not_even_two_mul_add_one (n : ℕ) : ¬ Even (2 * n + 1) :=
  odd_iff_not_even.1 <| odd_two_mul_add_one n

lemma even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align nat.even_sub' Nat.even_sub'

lemma Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) :=
  (le_total n m).elim (fun h ↦ by simp only [even_sub' h, *]) fun h ↦ by
    simp only [Nat.sub_eq_zero_iff_le.2 h, even_zero]
#align nat.odd.sub_odd Nat.Odd.sub_odd

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd

lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, even_mul]
#align nat.odd_mul Nat.odd_mul

lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1
#align nat.odd.of_mul_left Nat.Odd.of_mul_left

lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2
#align nat.odd.of_mul_right Nat.Odd.of_mul_right

lemma even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, ← Nat.mod_mul_right_div_self, mul_comm]
#align nat.even_div Nat.even_div

@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]
#align nat.odd_add Nat.odd_add

lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]
#align nat.odd_add' Nat.odd_add'

lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot ↦ by simp [hnot] at h
#align nat.ne_of_odd_add Nat.ne_of_odd_add

@[parity_simps] lemma odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub h, not_iff, odd_iff_not_even]
#align nat.odd_sub Nat.odd_sub

lemma Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) :=
  (odd_sub h).mpr <| iff_of_true hm hn
#align nat.odd.sub_even Nat.Odd.sub_even

lemma odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub h, not_iff, not_iff_comm, odd_iff_not_even]
#align nat.odd_sub' Nat.odd_sub'

lemma Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) :=
  (odd_sub' h).mpr <| iff_of_true hn hm
#align nat.even.sub_odd Nat.Even.sub_odd

lemma two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by
  rw [← odd_iff.mp h, div_add_mod]
#align nat.two_mul_div_two_add_one_of_odd Nat.two_mul_div_two_add_one_of_odd

lemma div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by
  rw [← odd_iff.mp h, div_add_mod']
#align nat.div_two_mul_two_add_one_of_odd Nat.div_two_mul_two_add_one_of_odd

lemma one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by
  rw [← odd_iff.mp h, mod_add_div']
#align nat.one_add_div_two_mul_two_of_odd Nat.one_add_div_two_mul_two_of_odd

set_option linter.deprecated false in
section

lemma bit0_div_two : bit0 n / 2 = n := Nat.bit0_inj $ by
  rw [bit0_eq_two_mul, two_mul_div_two_of_even (even_bit0 n)]
#align nat.bit0_div_two Nat.bit0_div_two

lemma bit1_div_two : bit1 n / 2 = n := Nat.bit1_inj $ by
  rw [bit1, bit0_eq_two_mul, Nat.two_mul_div_two_add_one_of_odd (odd_bit1 n)]
#align nat.bit1_div_two Nat.bit1_div_two

@[simp]
lemma bit0_div_bit0 : bit0 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul m, ← Nat.div_div_eq_div_mul, bit0_div_two]
#align nat.bit0_div_bit0 Nat.bit0_div_bit0

@[simp]
lemma bit1_div_bit0 : bit1 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul, ← Nat.div_div_eq_div_mul, bit1_div_two]
#align nat.bit1_div_bit0 Nat.bit1_div_bit0

@[simp]
lemma bit0_mod_bit0 : bit0 n % bit0 m = bit0 (n % m) := by
  rw [bit0_eq_two_mul n, bit0_eq_two_mul m, bit0_eq_two_mul (n % m), Nat.mul_mod_mul_left]
#align nat.bit0_mod_bit0 Nat.bit0_mod_bit0

@[simp]
lemma bit1_mod_bit0 : bit1 n % bit0 m = bit1 (n % m) := by
  have h₁ := congr_arg bit1 (Nat.div_add_mod n m)
  -- `∀ m n : ℕ, bit0 m * n = bit0 (m * n)` seems to be missing...
  rw [bit1_add, bit0_eq_two_mul, ← mul_assoc, ← bit0_eq_two_mul] at h₁
  have h₂ := Nat.div_add_mod (bit1 n) (bit0 m)
  rw [bit1_div_bit0] at h₂
  exact Nat.add_left_cancel (h₂.trans h₁.symm)
#align nat.bit1_mod_bit0 Nat.bit1_mod_bit0

end

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, two_ne_zero, parity_simps]

/- Porting note: the `simp` lemmas about `bit*` no longer apply. -/
example : ¬Even 25394535 := by decide

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type*} {f : α → α} {n : ℕ}

set_option linter.deprecated false in
section

lemma iterate_bit0 (hf : Involutive f) (n : ℕ) : f^[bit0 n] = id := by
  rw [bit0, ← two_mul, iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]
#align function.involutive.iterate_bit0 Function.Involutive.iterate_bit0

lemma iterate_bit1 (hf : Involutive f) (n : ℕ) : f^[bit1 n] = f := by
  rw [bit1, ← succ_eq_add_one, iterate_succ, hf.iterate_bit0, id_comp]
#align function.involutive.iterate_bit1 Function.Involutive.iterate_bit1

end

lemma iterate_two_mul (hf : Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

lemma iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, hf.iterate_two_mul]
#align function.involutive.iterate_even Function.Involutive.iterate_even

lemma iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f := by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add, hf.iterate_two_mul, id_comp, iterate_one]
#align function.involutive.iterate_odd Function.Involutive.iterate_odd

lemma iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H ↦ odd_iff_not_even.2 fun hn ↦ hne <| by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩
#align function.involutive.iterate_eq_self Function.Involutive.iterate_eq_self

lemma iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H ↦ even_iff_not_odd.2 fun hn ↦ hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩
#align function.involutive.iterate_eq_id Function.Involutive.iterate_eq_id

end Involutive
end Function

lemma neg_one_pow_eq_one_iff_even {R : Type*} [Monoid R] [HasDistribNeg R] {n : ℕ}
    (h : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ Even n where
  mp h' := of_not_not fun hn ↦ h <| (Odd.neg_one_pow <| odd_iff_not_even.mpr hn).symm.trans h'
  mpr := Even.neg_one_pow
#align neg_one_pow_eq_one_iff_even neg_one_pow_eq_one_iff_even
