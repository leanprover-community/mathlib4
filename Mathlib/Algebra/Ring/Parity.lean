/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Function.Iterate

/-!
# Even and odd elements in rings

This file defines odd elements and proves some general facts about even and odd elements of rings.

As opposed to `Even`, `Odd` does not have a multiplicative counterpart.

## TODO

Try to generalize `Even` lemmas further. For example, there are still a few lemmas whose `Semiring`
assumptions I (DT) am not convinced are necessary. If that turns out to be true, they could be moved
to `Mathlib/Algebra/Group/Even.lean`.

## See also

`Mathlib/Algebra/Group/Even.lean` for the definition of even elements.
-/

assert_not_exists DenselyOrdered

open MulOpposite

variable {F α β : Type*}

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ} {a : α}

@[simp] lemma Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]

lemma Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

lemma Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]

lemma Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]

end DivisionMonoid

@[simp] lemma IsSquare.zero [MulZeroClass α] : IsSquare (0 : α) := ⟨0, (mul_zero _).symm⟩

section Semiring
variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

lemma even_iff_exists_two_mul : Even a ↔ ∃ b, a = 2 * b := by simp [even_iff_exists_two_nsmul]

lemma even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd

lemma Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b :=
  even_iff_two_dvd.2 <| ha.two_dvd.trans hab

lemma Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b := ha.trans_dvd hab

@[simp] lemma range_two_mul (α) [NonAssocSemiring α] :
    Set.range (fun x : α ↦ 2 * x) = {a | Even a} := by
  ext x
  simp [eq_comm, two_mul, Even]

@[simp] lemma even_two : Even (2 : α) := ⟨1, by rw [one_add_one_eq_two]⟩

@[simp] lemma Even.mul_left (ha : Even a) (b) : Even (b * a) := ha.map (AddMonoidHom.mulLeft _)

@[simp] lemma Even.mul_right (ha : Even a) (b) : Even (a * b) := ha.map (AddMonoidHom.mulRight _)

lemma even_two_mul (a : α) : Even (2 * a) := ⟨a, two_mul _⟩

lemma Even.pow_of_ne_zero (ha : Even a) : ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
  | n + 1, _ => by rw [pow_succ]; exact ha.mul_left _

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop := ∃ k, a = 2 * k + 1

lemma odd_iff_exists_bit1 : Odd a ↔ ∃ b, a = 2 * b + 1 := exists_congr fun b ↦ by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1

@[simp] lemma range_two_mul_add_one (α : Type*) [Semiring α] :
    Set.range (fun x : α ↦ 2 * x + 1) = {a | Odd a} := by ext x; simp [Odd, eq_comm]

lemma Even.add_odd : Even a → Odd b → Odd (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩

lemma Even.odd_add (ha : Even a) (hb : Odd b) : Odd (b + a) := add_comm a b ▸ ha.add_odd hb
lemma Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := add_comm a b ▸ hb.add_odd ha

lemma Odd.add_odd : Odd a → Odd b → Even (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨a + b + 1, ?_⟩
  rw [two_mul, two_mul]
  ac_rfl

@[simp] lemma odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩

@[simp] lemma Even.add_one (h : Even a) : Odd (a + 1) := h.add_odd odd_one
@[simp] lemma Even.one_add (h : Even a) : Odd (1 + a) := h.odd_add odd_one
@[simp] lemma Odd.add_one (h : Odd a) : Even (a + 1) := h.add_odd odd_one
@[simp] lemma Odd.one_add (h : Odd a) : Even (1 + a) := odd_one.add_odd h

lemma odd_two_mul_add_one (a : α) : Odd (2 * a + 1) := ⟨_, rfl⟩

@[simp] lemma odd_add_self_one' : Odd (a + (a + 1)) := by simp [← add_assoc]
@[simp] lemma odd_add_one_self : Odd (a + 1 + a) := by simp [add_comm _ a]
@[simp] lemma odd_add_one_self' : Odd (a + (1 + a)) := by simp [add_comm 1 a]

lemma Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩

lemma Odd.natCast {R : Type*} [Semiring R] {n : ℕ} (hn : Odd n) : Odd (n : R) :=
  hn.map <| Nat.castRingHom R

@[simp] lemma Odd.mul : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨2 * a * b + b + a, ?_⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]

lemma Odd.pow {n : ℕ} (ha : Odd a) : Odd (a ^ n) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hrec => rw [pow_succ]; exact hrec.mul ha

lemma Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with | zero => simpa | succ k ih => ?_
  have : a ^ 2 = b ^ 2 := add_right_cancel <|
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul, ← pow_add, add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]

theorem Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Even a :=
  let ⟨u, hu⟩ := h; ⟨u⁻¹ * a, by rw [← mul_add, ← two_mul, ← hu, Units.inv_mul_cancel_left]⟩

theorem isUnit_two_iff_forall_even : IsUnit (2 : α) ↔ ∀ a : α, Even a := by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul, eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

end Semiring

section Ring
variable [Ring α]

theorem Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd a := by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

end Ring

section Monoid
variable [Monoid α] [HasDistribNeg α] {n : ℕ}

lemma Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]

@[simp] lemma Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]

end Monoid

section Ring
variable [Ring α] {a b : α} {n : ℕ}

lemma even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]

lemma Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right,
    ← neg_add, hk]

@[simp] lemma odd_neg : Odd (-a) ↔ Odd a := ⟨fun h ↦ neg_neg a ▸ h.neg, Odd.neg⟩

lemma odd_neg_one : Odd (-1 : α) := by simp

lemma Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_even hb.neg

lemma Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

lemma Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add_odd hb.neg

end Ring

namespace Nat
variable {m n : ℕ}

@[grind =]
lemma odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ ↦ by cutsat, fun h ↦ ⟨n / 2, by cutsat⟩⟩

instance : DecidablePred (Odd : ℕ → Prop) := fun _ ↦ decidable_of_iff _ odd_iff.symm

lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

@[simp, grind =] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by grind
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by grind

@[simp] lemma not_odd_zero : ¬Odd 0 := by grind

lemma _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by grind

lemma even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) := by grind

lemma even_or_odd (n : ℕ) : Even n ∨ Odd n := (even_xor_odd n).or

lemma even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using even_or_odd n

lemma even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := even_or_odd n <;>
  · use k
    grind

lemma odd_add_one {n : ℕ} : Odd (n + 1) ↔ ¬ Odd n := by grind

lemma mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 := by grind

@[simp] lemma mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 := by cutsat

@[simp] lemma succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 := by cutsat

lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

@[simp] lemma not_even_bit1 (n : ℕ) : ¬Even (2 * n + 1) := by simp [parity_simps]

lemma not_even_two_mul_add_one (n : ℕ) : ¬ Even (2 * n + 1) := by grind

lemma even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

lemma Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) := by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd

lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by grind

lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1

lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2

lemma odd_pow_iff {e : ℕ} (he : e ≠ 0) : Odd (n ^ e) ↔ Odd n := by grind

lemma even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, ← Nat.mod_mul_right_div_self, mul_comm]

@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by grind

lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind

lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind

@[parity_simps] lemma odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by grind

lemma Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) := by grind

lemma odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

lemma Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) := by grind

lemma two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by grind

lemma div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by grind

lemma one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by grind

lemma two_dvd_mul_add_one (k : ℕ) : 2 ∣ k * (k + 1) :=
  even_iff_two_dvd.mp (even_mul_succ_self k)

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, parity_simps]

example : ¬Even 25394535 := by decide

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type*} {f : α → α} {n : ℕ}

section

lemma iterate_bit0 (hf : Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

lemma iterate_bit1 (hf : Involutive f) (n : ℕ) : f^[2 * n + 1] = f := by
  rw [← succ_eq_add_one, iterate_succ, hf.iterate_bit0, id_comp]

end

lemma iterate_two_mul (hf : Involutive f) (n : ℕ) : f^[2 * n] = id := by
  rw [iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

lemma iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, hf.iterate_two_mul]

lemma iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f := by
  obtain ⟨m, rfl⟩ := hn
  rw [iterate_add, hf.iterate_two_mul, id_comp, iterate_one]

lemma iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H ↦ not_even_iff_odd.1 fun hn ↦ hne <| by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩

lemma iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H ↦ not_odd_iff_even.1 fun hn ↦ hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

end Involutive
end Function

section DistribNeg

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

lemma neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1 else (-1) := by
  cases even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]

lemma neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ m = (-1) ^ n := by
  simp [h, neg_one_pow_eq_ite]

lemma neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = 1 ↔ Even n := by simp [neg_one_pow_eq_ite, h]

lemma neg_one_pow_eq_neg_one_iff_odd (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = -1 ↔ Odd n := by simp [neg_one_pow_eq_ite, h.symm]

end DistribNeg

section CharTwo

-- We state the following theorems in terms of the slightly more general `2 = 0` hypothesis.

variable {R : Type*} [AddMonoidWithOne R]

private theorem natCast_eq_zero_or_one_of_two_eq_zero' (n : ℕ) (h : (2 : R) = 0) :
    (Even n → (n : R) = 0) ∧ (Odd n → (n : R) = 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]

theorem natCast_eq_zero_of_even_of_two_eq_zero {n : ℕ} (hn : Even n) (h : (2 : R) = 0) :
    (n : R) = 0 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn

theorem natCast_eq_one_of_odd_of_two_eq_zero {n : ℕ} (hn : Odd n) (h : (2 : R) = 0) :
    (n : R) = 1 :=
  (natCast_eq_zero_or_one_of_two_eq_zero' n h).2 hn

theorem natCast_eq_zero_or_one_of_two_eq_zero (n : ℕ) (h : (2 : R) = 0) :
    (n : R) = 0 ∨ (n : R) = 1 := by
  obtain hn | hn := Nat.even_or_odd n
  · exact Or.inl <| natCast_eq_zero_of_even_of_two_eq_zero hn h
  · exact Or.inr <| natCast_eq_one_of_odd_of_two_eq_zero hn h

end CharTwo
