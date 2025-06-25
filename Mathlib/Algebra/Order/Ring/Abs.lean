/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Absolute values in linear ordered rings.
-/


variable {α : Type*}

section LinearOrderedAddCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive] lemma mabs_zpow (n : ℤ) (a : α) : |a ^ n|ₘ = |a|ₘ ^ |n| := by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv, ← zpow_neg, ← abs_neg, h, zpow_natCast, Nat.abs_cast, zpow_natCast]
    exact mabs_pow m _

end LinearOrderedAddCommGroup

lemma odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a := by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : ℕ} {a b : α}

@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_pos zero_lt_one

lemma abs_two : |(2 : α)| = 2 := abs_of_pos zero_lt_two

lemma abs_mul (a b : α) : |a * b| = |a| * |b| := by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, eq_self_iff_true, neg_mul,
      mul_neg, neg_neg, *]

/-- `abs` as a `MonoidWithZeroHom`. -/
def absHom : α →*₀ α where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp]
lemma abs_pow (a : α) (n : ℕ) : |a ^ n| = |a| ^ n := (absHom.toMonoidHom : α →* α).map_pow _ _

lemma pow_abs (a : α) (n : ℕ) : |a| ^ n = |a ^ n| := (abs_pow a n).symm

lemma Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n := by
  rw [← abs_pow, abs_eq_self]; exact hn.pow_nonneg _

lemma abs_neg_one_pow (n : ℕ) : |(-1 : α) ^ n| = 1 := by rw [← pow_abs, abs_neg, abs_one, one_pow]

lemma abs_pow_eq_one (a : α) (h : n ≠ 0) : |a ^ n| = 1 ↔ |a| = 1 := by
  convert pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]

omit [IsStrictOrderedRing α] in
@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

@[simp]
lemma abs_mul_self (a : α) : |a * a| = a * a := by rw [abs_mul, abs_mul_abs_self]

lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

lemma abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

lemma abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 := by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)

omit [IsStrictOrderedRing α] in
@[simp] lemma sq_abs (a : α) : |a| ^ 2 = a ^ 2 := by simpa only [sq] using abs_mul_abs_self a

lemma abs_sq (x : α) : |x ^ 2| = x ^ 2 := by simpa only [sq] using abs_mul_self x

lemma sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b| := by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

lemma sq_lt_sq' (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2 :=
  sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

lemma sq_le_sq : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b| := by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)

lemma sq_le_sq' (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

lemma abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : |a| < b := by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]

lemma abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : -b < a ∧ a < b :=
  abs_lt.1 <| abs_lt_of_sq_lt_sq h hb

lemma abs_le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]

theorem le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b :=
  le_abs_self a |>.trans <| abs_le_of_sq_le_sq h hb

lemma abs_le_of_sq_le_sq' (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b :=
  abs_le.1 <| abs_le_of_sq_le_sq h hb

lemma sq_eq_sq_iff_abs_eq_abs (a b : α) : a ^ 2 = b ^ 2 ↔ |a| = |b| := by
  simp only [le_antisymm_iff, sq_le_sq]

@[simp] lemma sq_le_one_iff_abs_le_one (a : α) : a ^ 2 ≤ 1 ↔ |a| ≤ 1 := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := a) (b := 1)

@[simp] lemma sq_lt_one_iff_abs_lt_one (a : α) : a ^ 2 < 1 ↔ |a| < 1 := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := a) (b := 1)

@[simp] lemma one_le_sq_iff_one_le_abs (a : α) : 1 ≤ a ^ 2 ↔ 1 ≤ |a| := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := 1) (b := a)

@[simp] lemma one_lt_sq_iff_one_lt_abs (a : α) : 1 < a ^ 2 ↔ 1 < |a| := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := 1) (b := a)

lemma exists_abs_lt {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (a : α) : ∃ b > 0, |a| < b :=
  ⟨|a| + 1, lt_of_lt_of_le zero_lt_one <| by simp, lt_add_one |a|⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) (n : ℕ)

omit [IsStrictOrderedRing α] in
theorem abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b := by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]

lemma abs_unit_intCast (a : ℤˣ) : |((a : ℤ) : α)| = 1 := by
  cases Int.units_eq_one_or a <;> simp_all

private def geomSum : ℕ → α
  | 0 => 1
  | n + 1 => a * geomSum n + b ^ (n + 1)

private theorem abs_geomSum_le : |geomSum a b n| ≤ (n + 1) * max |a| |b| ^ n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul, abs_pow, Nat.cast_succ, add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ, ← mul_assoc, mul_comm |a|]
  exact mul_le_mul ih le_sup_left (abs_nonneg _) (mul_nonneg
    (@Nat.cast_succ α .. ▸ Nat.cast_nonneg _) <| pow_nonneg ((abs_nonneg _).trans le_sup_left) _)

omit [LinearOrder α] [IsStrictOrderedRing α] in
private theorem pow_sub_pow_eq_sub_mul_geomSum :
    a ^ (n + 1) - b ^ (n + 1) = (a - b) * geomSum a b n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum, mul_add, mul_comm a, ← mul_assoc, ← ih,
    sub_mul, sub_mul, ← pow_succ, ← pow_succ', mul_comm, sub_add_sub_cancel]

theorem abs_pow_sub_pow_le : |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := by
  obtain _ | n := n; · simp
  rw [Nat.add_sub_cancel, pow_sub_pow_eq_sub_mul_geomSum, abs_mul, mul_assoc, Nat.cast_succ]
  gcongr
  · exact abs_nonneg _
  · exact abs_geomSum_le ..

end LinearOrderedCommRing

section

variable [Ring α] [LinearOrder α]

@[simp]
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by
  rcases abs_choice a with h | h <;> simp only [h, neg_dvd]

theorem abs_dvd_self (a : α) : |a| ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)

@[simp]
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by
  rcases abs_choice b with h | h <;> simp only [h, dvd_neg]

theorem self_dvd_abs (a : α) : a ∣ |a| :=
  (dvd_abs a a).mpr (dvd_refl a)

theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)

end

open Nat

section LinearOrderedRing
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {n : ℕ}

lemma pow_eq_pow_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]

lemma pow_eq_pow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

lemma pow_eq_one_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_of_ne_zero hn]

lemma pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_cases]

lemma pow_eq_neg_pow_iff (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]

lemma pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

end LinearOrderedRing

variable {m n a : ℕ}

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
lemma Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
lemma Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a) := (Odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
lemma Even.mod_even (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn

lemma Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m :=
  not_even_iff_odd.1 <| mt hm.even (not_even_iff_odd.2 hn)

/-- `2` is not a factor of an odd natural number. -/
lemma Odd.ne_two_of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : m ≠ 2 := by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)
