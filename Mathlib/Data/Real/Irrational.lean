/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_rat`, `Irrational.rat_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/


open Rat Real

/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b := by
  simp [Irrational, Rat.forall, eq_comm]

theorem Irrational.ne_rational {x : ℝ} (hx : Irrational x) (a b : ℤ) : x ≠ a / b := by
  rintro rfl; exact hx ⟨a / b, by simp⟩

/-- A transcendental real number is irrational. -/
theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

/-!
### Irrationality of roots of integer and rational numbers
-/


/-- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m)
    (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x := by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : ℤ) : ℝ) ≠ 0 := by
    rw [Int.cast_ne_zero, Int.natCast_ne_zero]
    exact P
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1
  rw [mk'_eq_divInt, cast_pow, cast_divInt, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow,
    ← Int.cast_pow, ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.natCast_pow, Int.natCast_dvd_natCast, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk'_eq_divInt, Int.ofNat_one, divInt_one, cast_intCast]

/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : multiplicity (p : ℤ) m % n ≠ 0) :
    Irrational x := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity_of_one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one))] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow, Int.cast_inj] at hxr
  subst m
  have : y ≠ 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  rw [(Int.finiteMultiplicity_iff.2 ⟨by simp [hp.1.ne_one], this⟩).multiplicity_pow
    (Nat.prime_iff_prime_int.1 hp.1), Nat.mul_mod_right] at hv
  exact hv rfl

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : ℤ) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg.2 <| le_of_lt hm)) (by rw [Hpv]; exact one_ne_zero)

@[simp] theorem not_irrational_zero : ¬Irrational 0 := not_not_intro ⟨0, Rat.cast_zero⟩
@[simp] theorem not_irrational_one : ¬Irrational 1 := not_not_intro ⟨1, Rat.cast_one⟩

theorem irrational_sqrt_ratCast_iff_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    Irrational (√q) ↔ ¬IsSquare q := by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := ℝ) ?_⟩
    rw [Rat.cast_mul, hy, mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩

theorem irrational_sqrt_ratCast_iff {q : ℚ} :
    Irrational (√q) ↔ ¬IsSquare q ∧ 0 ≤ q := by
  obtain hq | hq := le_or_gt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]

theorem irrational_sqrt_intCast_iff_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    Irrational (√z) ↔ ¬IsSquare z := by
  rw [← Rat.isSquare_intCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz),
    Rat.cast_intCast]

theorem irrational_sqrt_intCast_iff {z : ℤ} :
    Irrational (√z) ↔ ¬IsSquare z ∧ 0 ≤ z := by
  rw [← Rat.cast_intCast, irrational_sqrt_ratCast_iff, Rat.isSquare_intCast_iff, Int.cast_nonneg]

theorem irrational_sqrt_natCast_iff {n : ℕ} : Irrational (√n) ↔ ¬IsSquare n := by
  rw [← Rat.isSquare_natCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg,
    Rat.cast_natCast]

theorem irrational_sqrt_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    Irrational √(ofNat(n)) ↔ ¬IsSquare ofNat(n) :=
  irrational_sqrt_natCast_iff

theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare

/-- **Irrationality of the Square Root of 2** -/
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt

/--
This can be used as
```lean
unseal Nat.sqrt.iter in
example : Irrational √24 := by decide
```
-/
instance {n : ℕ} [n.AtLeastTwo] : Decidable (Irrational √(ofNat(n))) :=
  decidable_of_iff' _ irrational_sqrt_ofNat_iff

instance (n : ℕ) : Decidable (Irrational (√n)) :=
  decidable_of_iff' _ irrational_sqrt_natCast_iff

instance (z : ℤ) : Decidable (Irrational (√z)) :=
  decidable_of_iff' _ irrational_sqrt_intCast_iff

instance (q : ℚ) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ irrational_sqrt_ratCast_iff

/-!
### Dot-style operations on `Irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/


namespace Irrational

variable {x : ℝ}

/-!
#### Irrational number is not equal to a rational/integer/natural number
-/


theorem ne_rat (h : Irrational x) (q : ℚ) : x ≠ q := fun hq => h ⟨q, hq.symm⟩

theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _

theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m

theorem ne_zero (h : Irrational x) : x ≠ 0 := mod_cast h.ne_nat 0

theorem ne_one (h : Irrational x) : x ≠ 1 := by simpa only [Nat.cast_one] using h.ne_nat 1

@[simp] theorem ne_ofNat (h : Irrational x) (n : ℕ) [n.AtLeastTwo] : x ≠ ofNat(n) :=
  h.ne_nat n

end Irrational

@[simp]
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩

@[simp]
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl

@[simp]
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl

@[simp] theorem not_irrational_ofNat (n : ℕ) [n.AtLeastTwo] : ¬Irrational ofNat(n) :=
  n.not_irrational
namespace Irrational

variable (q : ℚ) {x y : ℝ}

/-!
#### Addition of rational/integer/natural numbers
-/


/-- If `x + y` is irrational, then at least one of `x` and `y` is irrational. -/
theorem add_cases : Irrational (x + y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩

theorem of_ratCast_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational
@[deprecated (since := "2025-04-01")] alias of_rat_add := of_ratCast_add

theorem ratCast_add (h : Irrational x) : Irrational (q + x) :=
  of_ratCast_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]
@[deprecated (since := "2025-04-01")] alias rat_add := ratCast_add

theorem of_add_ratCast : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_ratCast_add q
@[deprecated (since := "2025-04-01")] alias of_add_rat := of_add_ratCast

theorem add_ratCast (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.ratCast_add q
@[deprecated (since := "2025-04-01")] alias add_rat := add_ratCast

theorem of_intCast_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by
  rw [← cast_intCast] at h
  exact h.of_ratCast_add m
@[deprecated (since := "2025-04-01")] alias of_int_add := of_intCast_add

theorem of_add_intCast (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_intCast_add m <| add_comm x m ▸ h
@[deprecated (since := "2025-04-01")] alias of_add_int := of_add_intCast

theorem intCast_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by
  rw [← cast_intCast]
  exact h.ratCast_add m
@[deprecated (since := "2025-04-01")] alias int_add := intCast_add


theorem add_intCast (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.intCast_add m
@[deprecated (since := "2025-04-01")] alias add_int := add_intCast

theorem of_natCast_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_intCast_add m
@[deprecated (since := "2025-04-01")] alias of_nat_add := of_natCast_add

theorem of_add_natCast (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_intCast m
@[deprecated (since := "2025-04-01")] alias of_add_nat := of_add_natCast

theorem natCast_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.intCast_add m
@[deprecated (since := "2025-04-01")] alias nat_add := natCast_add

theorem add_natCast (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_intCast m
@[deprecated (since := "2025-04-01")] alias add_nat := add_natCast

/-!
#### Negation
-/


theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]

/-!
#### Subtraction of rational/integer/natural numbers
-/


theorem sub_ratCast (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_ratCast (-q)
@[deprecated (since := "2025-04-01")] alias sub_rat := sub_ratCast

theorem ratCast_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.ratCast_add q
@[deprecated (since := "2025-04-01")] alias rat_sub := ratCast_sub

theorem of_sub_ratCast (h : Irrational (x - q)) : Irrational x :=
  of_add_ratCast (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h
@[deprecated (since := "2025-04-01")] alias of_sub_rat := of_sub_ratCast

theorem of_ratCast_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))
@[deprecated (since := "2025-04-01")] alias of_rat_sub := of_ratCast_sub

theorem sub_intCast (h : Irrational x) (m : ℤ) : Irrational (x - m) := by
  simpa only [Rat.cast_intCast] using h.sub_ratCast m
@[deprecated (since := "2025-04-01")] alias sub_int := sub_intCast

theorem intCast_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by
  simpa only [Rat.cast_intCast] using h.ratCast_sub m
@[deprecated (since := "2025-04-01")] alias int_sub := intCast_sub

theorem of_sub_intCast (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_ratCast m <| by rwa [Rat.cast_intCast]
@[deprecated (since := "2025-04-01")] alias of_sub_int := of_sub_intCast

theorem of_intCast_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_ratCast_sub m <| by rwa [Rat.cast_intCast]
@[deprecated (since := "2025-04-01")] alias of_int_sub := of_intCast_sub

theorem sub_natCast (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_intCast m
@[deprecated (since := "2025-04-01")] alias sub_nat := sub_natCast

theorem natCast_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.intCast_sub m
@[deprecated (since := "2025-04-01")] alias nat_sub := natCast_sub

theorem of_sub_natCast (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_intCast m
@[deprecated (since := "2025-04-01")] alias of_sub_nat := of_sub_natCast

theorem of_natCast_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_intCast_sub m
@[deprecated (since := "2025-04-01")] alias of_nat_sub := of_natCast_sub

/-!
#### Multiplication by rational numbers
-/


theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩

theorem of_mul_ratCast (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
@[deprecated (since := "2025-04-01")] alias of_mul_rat := of_mul_ratCast

theorem mul_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x * q) :=
  of_mul_ratCast q⁻¹ <| by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]
@[deprecated (since := "2025-04-01")] alias mul_rat := mul_ratCast

theorem of_ratCast_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_ratCast q
@[deprecated (since := "2025-04-01")] alias of_rat_mul := of_ratCast_mul

theorem ratCast_mul (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_ratCast hq
@[deprecated (since := "2025-04-01")] alias rat_mul := ratCast_mul

theorem of_mul_intCast (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_ratCast m <| by rwa [cast_intCast]
@[deprecated (since := "2025-04-01")] alias of_mul_int := of_mul_intCast

theorem of_intCast_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_ratCast_mul m <| by rwa [cast_intCast]
@[deprecated (since := "2025-04-01")] alias of_int_mul := of_intCast_mul

theorem mul_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x * m) := by
  rw [← cast_intCast]
  refine h.mul_ratCast ?_
  rwa [Int.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias mul_int := mul_intCast

theorem intCast_mul (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_intCast hm
@[deprecated (since := "2025-04-01")] alias int_mul := intCast_mul

theorem of_mul_natCast (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_intCast m
@[deprecated (since := "2025-04-01")] alias of_mul_nat := of_mul_natCast

theorem of_natCast_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_intCast_mul m
@[deprecated (since := "2025-04-01")] alias of_nat_mul := of_natCast_mul

theorem mul_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x * m) :=
  h.mul_intCast <| Int.natCast_ne_zero.2 hm
@[deprecated (since := "2025-04-01")] alias mul_nat := mul_natCast

theorem natCast_mul (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m * x) :=
  h.intCast_mul <| Int.natCast_ne_zero.2 hm
@[deprecated (since := "2025-04-01")] alias nat_mul := natCast_mul

/-!
#### Inverse
-/


theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩

protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]

/-!
#### Division
-/


theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv

theorem of_ratCast_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_ratCast_mul q).of_inv
@[deprecated (since := "2025-04-01")] alias of_rat_div := of_ratCast_div

theorem of_div_ratCast (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
@[deprecated (since := "2025-04-01")] alias of_div_rat := of_div_ratCast

theorem ratCast_div (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q / x) :=
  h.inv.ratCast_mul hq
@[deprecated (since := "2025-04-01")] alias rat_div := ratCast_div

theorem div_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x / q) := by
  rw [div_eq_mul_inv, ← cast_inv]
  exact h.mul_ratCast (inv_ne_zero hq)
@[deprecated (since := "2025-04-01")] alias div_rat := div_ratCast

theorem of_intCast_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
@[deprecated (since := "2025-04-01")] alias of_int_div := of_intCast_div

theorem of_div_intCast (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
@[deprecated (since := "2025-04-01")] alias of_div_int := of_div_intCast

theorem intCast_div (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.intCast_mul hm
@[deprecated (since := "2025-04-01")] alias int_div := intCast_div

theorem div_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x / m) := by
  rw [← cast_intCast]
  refine h.div_ratCast ?_
  rwa [Int.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias div_int := div_intCast

theorem of_natCast_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_intCast_div m
@[deprecated (since := "2025-04-01")] alias of_nat_div := of_natCast_div

theorem of_div_natCast (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_intCast m
@[deprecated (since := "2025-04-01")] alias of_div_nat := of_div_natCast

theorem natCast_div (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.natCast_mul hm
@[deprecated (since := "2025-04-01")] alias nat_div := natCast_div

theorem div_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x / m) :=
  h.div_intCast <| by rwa [Int.natCast_ne_zero]
@[deprecated (since := "2025-04-01")] alias div_nat := div_natCast

theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_ratCast_div 1 <| by rwa [cast_one]

/-!
#### Natural and integer power
-/


theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id

theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x
  | 0 => fun h => by
    rw [pow_zero] at h
    exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by
    rw [pow_succ] at h
    exact h.mul_cases.elim (of_pow n) id

open Int in
theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x
  | (n : ℕ) => fun h => by
    rw [zpow_natCast] at h
    exact h.of_pow _
  | -[n+1] => fun h => by
    rw [zpow_negSucc] at h
    exact h.of_inv.of_pow _

end Irrational

section Polynomial

open Polynomial

variable (x : ℝ) (p : ℤ[X])

theorem one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p ≠ 0)
    (x_is_root : aeval x p = 0) : 1 < p.natDegree := by
  by_contra rid
  rcases exists_eq_X_add_C_of_natDegree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩
  clear rid
  have : (a : ℝ) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simp at p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    · refine hx ⟨-b / a, ?_⟩
      assumption_mod_cast
    · assumption_mod_cast

end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/


@[simp]
theorem irrational_ratCast_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_ratCast_add q, ratCast_add q⟩
@[deprecated (since := "2025-04-01")] alias irrational_rat_add_iff := irrational_ratCast_add_iff

@[simp]
theorem irrational_intCast_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[deprecated (since := "2025-04-01")] alias irrational_int_add_iff := irrational_intCast_add_iff

@[simp]
theorem irrational_natCast_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[deprecated (since := "2025-04-01")] alias irrational_nat_add_iff := irrational_natCast_add_iff

@[simp]
theorem irrational_add_ratCast_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_ratCast q, add_ratCast q⟩
@[deprecated (since := "2025-04-01")] alias irrational_add_rat_iff := irrational_add_ratCast_iff

@[simp]
theorem irrational_add_intCast_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[deprecated (since := "2025-04-01")] alias irrational_add_int_iff := irrational_add_intCast_iff

@[simp]
theorem irrational_add_natCast_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[deprecated (since := "2025-04-01")] alias irrational_add_nat_iff := irrational_add_natCast_iff

@[simp]
theorem irrational_ratCast_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_ratCast_sub q, ratCast_sub q⟩
@[deprecated (since := "2025-04-01")] alias irrational_rat_sub_iff := irrational_ratCast_sub_iff

@[simp]
theorem irrational_intCast_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[deprecated (since := "2025-04-01")] alias irrational_int_sub_iff := irrational_intCast_sub_iff

@[simp]
theorem irrational_natCast_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[deprecated (since := "2025-04-01")] alias irrational_nat_sub_iff := irrational_natCast_sub_iff

@[simp]
theorem irrational_sub_ratCast_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_ratCast q, sub_ratCast q⟩
@[deprecated (since := "2025-04-01")] alias irrational_sub_rat_iff := irrational_sub_ratCast_iff

@[simp]
theorem irrational_sub_intCast_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[deprecated (since := "2025-04-01")] alias irrational_sub_int_iff := irrational_sub_intCast_iff

@[simp]
theorem irrational_sub_natCast_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[deprecated (since := "2025-04-01")] alias irrational_sub_nat_iff := irrational_sub_natCast_iff

@[simp]
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩

@[simp]
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩

@[simp]
theorem irrational_ratCast_mul_iff : Irrational (q * x) ↔ q ≠ 0 ∧ Irrational x :=
  ⟨fun h => ⟨Rat.cast_ne_zero.1 <| left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[deprecated (since := "2025-04-01")] alias irrational_rat_mul_iff := irrational_ratCast_mul_iff

@[simp]
theorem irrational_mul_ratCast_iff : Irrational (x * q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [mul_comm, irrational_ratCast_mul_iff]
@[deprecated (since := "2025-04-01")] alias irrational_mul_rat_iff := irrational_mul_ratCast_iff

@[simp]
theorem irrational_intCast_mul_iff : Irrational (m * x) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_ratCast_mul_iff, Int.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_int_mul_iff := irrational_intCast_mul_iff

@[simp]
theorem irrational_mul_intCast_iff : Irrational (x * m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_mul_ratCast_iff, Int.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_mul_int_iff := irrational_mul_intCast_iff

@[simp]
theorem irrational_natCast_mul_iff : Irrational (n * x) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_ratCast_mul_iff, Nat.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_nat_mul_iff := irrational_natCast_mul_iff

@[simp]
theorem irrational_mul_natCast_iff : Irrational (x * n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_mul_ratCast_iff, Nat.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_mul_nat_iff := irrational_mul_natCast_iff

@[simp]
theorem irrational_ratCast_div_iff : Irrational (q / x) ↔ q ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[deprecated (since := "2025-04-01")] alias irrational_rat_div_iff := irrational_ratCast_div_iff

@[simp]
theorem irrational_div_ratCast_iff : Irrational (x / q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [div_eq_mul_inv, ← cast_inv, irrational_mul_ratCast_iff, Ne, inv_eq_zero]
@[deprecated (since := "2025-04-01")] alias irrational_div_rat_iff := irrational_div_ratCast_iff

@[simp]
theorem irrational_intCast_div_iff : Irrational (m / x) ↔ m ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[deprecated (since := "2025-04-01")] alias irrational_int_div_iff := irrational_intCast_div_iff

@[simp]
theorem irrational_div_intCast_iff : Irrational (x / m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_div_ratCast_iff, Int.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_div_int_iff := irrational_div_intCast_iff

@[simp]
theorem irrational_natCast_div_iff : Irrational (n / x) ↔ n ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
@[deprecated (since := "2025-04-01")] alias irrational_nat_div_iff := irrational_natCast_div_iff

@[simp]
theorem irrational_div_natCast_iff : Irrational (x / n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_div_ratCast_iff, Nat.cast_ne_zero]
@[deprecated (since := "2025-04-01")] alias irrational_div_nat_iff := irrational_div_natCast_iff

/-- There is an irrational number `r` between any two reals `x < r < y`. -/
theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

end
