/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
import Mathlib.Data.Rat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Algebraic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.IntervalCases

#align_import data.real.irrational from "leanprover-community/mathlib"@"7e7aaccf9b0182576cabdde36cf1b5ad3585b70d"

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `sqrt q` is irrational if and only if
`Rat.sqrt q * Rat.sqrt q ≠ q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_rat`, `Irrational.rat_sub` etc.
-/


open Rat Real multiplicity

/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)
#align irrational Irrational

theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, x ≠ a / b := by
  simp only [Irrational, Rat.forall, cast_mk, not_exists, Set.mem_range, cast_intCast, cast_div,
    eq_comm]
#align irrational_iff_ne_rational irrational_iff_ne_rational

/-- A transcendental real number is irrational. -/
theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)
#align transcendental.irrational Transcendental.irrational

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
  rw [mk'_eq_divInt, cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow,
    ← Int.cast_pow, ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.natCast_pow, Int.natCast_dvd_natCast, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk'_eq_divInt, Int.ofNat_one, divInt_one, cast_intCast]
#align irrational_nrt_of_notint_nrt irrational_nrt_of_notint_nrt

/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.1.ne_one, hm⟩) % n ≠ 0) :
    Irrational x := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simp [hxr, multiplicity.one_right (mt isUnit_iff_dvd_one.1
      (mt Int.natCast_dvd_natCast.1 hp.1.not_dvd_one)), Nat.zero_mod] at hv
  refine irrational_nrt_of_notint_nrt _ _ hxr ?_ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow, Int.cast_inj] at hxr
  subst m
  have : y ≠ 0 := by rintro rfl; rw [zero_pow hnpos.ne'] at hm; exact hm rfl
  erw [multiplicity.pow' (Nat.prime_iff_prime_int.1 hp.1) (finite_int_iff.2 ⟨hp.1.ne_one, this⟩),
    Nat.mul_mod_right] at hv
  exact hv rfl
#align irrational_nrt_of_n_not_dvd_multiplicity irrational_nrt_of_n_not_dvd_multiplicity

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv :
      (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.1.ne_one, (ne_of_lt hm).symm⟩) % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg.2 <| le_of_lt hm)) (by rw [Hpv]; exact one_ne_zero)
#align irrational_sqrt_of_multiplicity_odd irrational_sqrt_of_multiplicity_odd

theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  @irrational_sqrt_of_multiplicity_odd p (Int.natCast_pos.2 hp.pos) p ⟨hp⟩ <| by
    simp [multiplicity.multiplicity_self
      (mt isUnit_iff_dvd_one.1 (mt Int.natCast_dvd_natCast.1 hp.not_dvd_one))]
#align nat.prime.irrational_sqrt Nat.Prime.irrational_sqrt

/-- **Irrationality of the Square Root of 2** -/
theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt
#align irrational_sqrt_two irrational_sqrt_two

theorem irrational_sqrt_rat_iff (q : ℚ) :
    Irrational (√q) ↔ Rat.sqrt q * Rat.sqrt q ≠ q ∧ 0 ≤ q :=
  if H1 : Rat.sqrt q * Rat.sqrt q = q then
    iff_of_false
      (not_not_intro
        ⟨Rat.sqrt q, by
          rw [← H1, cast_mul, sqrt_mul_self (cast_nonneg.2 <| Rat.sqrt_nonneg q), sqrt_eq,
            abs_of_nonneg (Rat.sqrt_nonneg q)]⟩)
      fun h => h.1 H1
  else
    if H2 : 0 ≤ q then
      iff_of_true
        (fun ⟨r, hr⟩ =>
          H1 <|
            (exists_mul_self _).1
              ⟨r, by
                rwa [eq_comm, sqrt_eq_iff_mul_self_eq (cast_nonneg.2 H2), ← cast_mul,
                      Rat.cast_inj] at hr
                rw [← hr]
                exact Real.sqrt_nonneg _⟩)
        ⟨H1, H2⟩
    else
      iff_of_false
        (not_not_intro
          ⟨0, by
            rw [cast_zero]
            exact (sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 <| le_of_not_le H2)).symm⟩)
        fun h => H2 h.2
#align irrational_sqrt_rat_iff irrational_sqrt_rat_iff

instance (q : ℚ) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ (irrational_sqrt_rat_iff q)

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
#align irrational.ne_rat Irrational.ne_rat

theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _
#align irrational.ne_int Irrational.ne_int

theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m
#align irrational.ne_nat Irrational.ne_nat

theorem ne_zero (h : Irrational x) : x ≠ 0 := mod_cast h.ne_nat 0
#align irrational.ne_zero Irrational.ne_zero

theorem ne_one (h : Irrational x) : x ≠ 1 := by simpa only [Nat.cast_one] using h.ne_nat 1
#align irrational.ne_one Irrational.ne_one

end Irrational

@[simp]
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩
#align rat.not_irrational Rat.not_irrational

@[simp]
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl
#align int.not_irrational Int.not_irrational

@[simp]
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl
#align nat.not_irrational Nat.not_irrational

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
#align irrational.add_cases Irrational.add_cases

theorem of_rat_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational
#align irrational.of_rat_add Irrational.of_rat_add

theorem rat_add (h : Irrational x) : Irrational (q + x) :=
  of_rat_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]
#align irrational.rat_add Irrational.rat_add

theorem of_add_rat : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_rat_add q
#align irrational.of_add_rat Irrational.of_add_rat

theorem add_rat (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.rat_add q
#align irrational.add_rat Irrational.add_rat

theorem of_int_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by
  rw [← cast_intCast] at h
  exact h.of_rat_add m
#align irrational.of_int_add Irrational.of_int_add

theorem of_add_int (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_int_add m <| add_comm x m ▸ h
#align irrational.of_add_int Irrational.of_add_int

theorem int_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by
  rw [← cast_intCast]
  exact h.rat_add m
#align irrational.int_add Irrational.int_add

theorem add_int (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.int_add m
#align irrational.add_int Irrational.add_int

theorem of_nat_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_int_add m
#align irrational.of_nat_add Irrational.of_nat_add

theorem of_add_nat (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_int m
#align irrational.of_add_nat Irrational.of_add_nat

theorem nat_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.int_add m
#align irrational.nat_add Irrational.nat_add

theorem add_nat (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_int m
#align irrational.add_nat Irrational.add_nat

/-!
#### Negation
-/


theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩
#align irrational.of_neg Irrational.of_neg

protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]
#align irrational.neg Irrational.neg

/-!
#### Subtraction of rational/integer/natural numbers
-/


theorem sub_rat (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_rat (-q)
#align irrational.sub_rat Irrational.sub_rat

theorem rat_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.rat_add q
#align irrational.rat_sub Irrational.rat_sub

theorem of_sub_rat (h : Irrational (x - q)) : Irrational x :=
  of_add_rat (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h
#align irrational.of_sub_rat Irrational.of_sub_rat

theorem of_rat_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_rat_add q (by simpa only [sub_eq_add_neg] using h))
#align irrational.of_rat_sub Irrational.of_rat_sub

theorem sub_int (h : Irrational x) (m : ℤ) : Irrational (x - m) := by
  simpa only [Rat.cast_intCast] using h.sub_rat m
#align irrational.sub_int Irrational.sub_int

theorem int_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by
  simpa only [Rat.cast_intCast] using h.rat_sub m
#align irrational.int_sub Irrational.int_sub

theorem of_sub_int (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_rat m <| by rwa [Rat.cast_intCast]
#align irrational.of_sub_int Irrational.of_sub_int

theorem of_int_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_rat_sub m <| by rwa [Rat.cast_intCast]
#align irrational.of_int_sub Irrational.of_int_sub

theorem sub_nat (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_int m
#align irrational.sub_nat Irrational.sub_nat

theorem nat_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.int_sub m
#align irrational.nat_sub Irrational.nat_sub

theorem of_sub_nat (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_int m
#align irrational.of_sub_nat Irrational.of_sub_nat

theorem of_nat_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_int_sub m
#align irrational.of_nat_sub Irrational.of_nat_sub

/-!
#### Multiplication by rational numbers
-/


theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩
#align irrational.mul_cases Irrational.mul_cases

theorem of_mul_rat (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
#align irrational.of_mul_rat Irrational.of_mul_rat

theorem mul_rat (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x * q) :=
  of_mul_rat q⁻¹ <| by rwa [mul_assoc, ← cast_mul, mul_inv_cancel hq, cast_one, mul_one]
#align irrational.mul_rat Irrational.mul_rat

theorem of_rat_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_rat q
#align irrational.of_rat_mul Irrational.of_rat_mul

theorem rat_mul (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_rat hq
#align irrational.rat_mul Irrational.rat_mul

theorem of_mul_int (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_rat m <| by rwa [cast_intCast]
#align irrational.of_mul_int Irrational.of_mul_int

theorem of_int_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_rat_mul m <| by rwa [cast_intCast]
#align irrational.of_int_mul Irrational.of_int_mul

theorem mul_int (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x * m) := by
  rw [← cast_intCast]
  refine h.mul_rat ?_
  rwa [Int.cast_ne_zero]
#align irrational.mul_int Irrational.mul_int

theorem int_mul (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_int hm
#align irrational.int_mul Irrational.int_mul

theorem of_mul_nat (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_int m
#align irrational.of_mul_nat Irrational.of_mul_nat

theorem of_nat_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_int_mul m
#align irrational.of_nat_mul Irrational.of_nat_mul

theorem mul_nat (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x * m) :=
  h.mul_int <| Int.natCast_ne_zero.2 hm
#align irrational.mul_nat Irrational.mul_nat

theorem nat_mul (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m * x) :=
  h.int_mul <| Int.natCast_ne_zero.2 hm
#align irrational.nat_mul Irrational.nat_mul

/-!
#### Inverse
-/


theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩
#align irrational.of_inv Irrational.of_inv

protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]
#align irrational.inv Irrational.inv

/-!
#### Division
-/


theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv
#align irrational.div_cases Irrational.div_cases

theorem of_rat_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_rat_mul q).of_inv
#align irrational.of_rat_div Irrational.of_rat_div

theorem of_div_rat (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
#align irrational.of_div_rat Irrational.of_div_rat

theorem rat_div (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q / x) :=
  h.inv.rat_mul hq
#align irrational.rat_div Irrational.rat_div

theorem div_rat (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x / q) := by
  rw [div_eq_mul_inv, ← cast_inv]
  exact h.mul_rat (inv_ne_zero hq)
#align irrational.div_rat Irrational.div_rat

theorem of_int_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
#align irrational.of_int_div Irrational.of_int_div

theorem of_div_int (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
#align irrational.of_div_int Irrational.of_div_int

theorem int_div (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.int_mul hm
#align irrational.int_div Irrational.int_div

theorem div_int (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x / m) := by
  rw [← cast_intCast]
  refine h.div_rat ?_
  rwa [Int.cast_ne_zero]
#align irrational.div_int Irrational.div_int

theorem of_nat_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_int_div m
#align irrational.of_nat_div Irrational.of_nat_div

theorem of_div_nat (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_int m
#align irrational.of_div_nat Irrational.of_div_nat

theorem nat_div (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.nat_mul hm
#align irrational.nat_div Irrational.nat_div

theorem div_nat (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x / m) :=
  h.div_int <| by rwa [Int.natCast_ne_zero]
#align irrational.div_nat Irrational.div_nat

theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_rat_div 1 <| by rwa [cast_one]
#align irrational.of_one_div Irrational.of_one_div

/-!
#### Natural and integer power
-/


theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id
#align irrational.of_mul_self Irrational.of_mul_self

theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x
  | 0 => fun h => by
    rw [pow_zero] at h
    exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by
    rw [pow_succ] at h
    exact h.mul_cases.elim (of_pow n) id
#align irrational.of_pow Irrational.of_pow

open Int in
theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x
  | (n : ℕ) => fun h => by
    rw [zpow_natCast] at h
    exact h.of_pow _
  | -[n+1] => fun h => by
    rw [zpow_negSucc] at h
    exact h.of_inv.of_pow _
#align irrational.of_zpow Irrational.of_zpow

end Irrational

section Polynomial

open Polynomial

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
#align one_lt_nat_degree_of_irrational_root one_lt_natDegree_of_irrational_root

end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/


@[simp]
theorem irrational_rat_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_rat_add q, rat_add q⟩
#align irrational_rat_add_iff irrational_rat_add_iff

@[simp]
theorem irrational_int_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_int_add m, fun h => h.int_add m⟩
#align irrational_int_add_iff irrational_int_add_iff

@[simp]
theorem irrational_nat_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_nat_add n, fun h => h.nat_add n⟩
#align irrational_nat_add_iff irrational_nat_add_iff

@[simp]
theorem irrational_add_rat_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_rat q, add_rat q⟩
#align irrational_add_rat_iff irrational_add_rat_iff

@[simp]
theorem irrational_add_int_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_int m, fun h => h.add_int m⟩
#align irrational_add_int_iff irrational_add_int_iff

@[simp]
theorem irrational_add_nat_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_nat n, fun h => h.add_nat n⟩
#align irrational_add_nat_iff irrational_add_nat_iff

@[simp]
theorem irrational_rat_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_rat_sub q, rat_sub q⟩
#align irrational_rat_sub_iff irrational_rat_sub_iff

@[simp]
theorem irrational_int_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_int_sub m, fun h => h.int_sub m⟩
#align irrational_int_sub_iff irrational_int_sub_iff

@[simp]
theorem irrational_nat_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_nat_sub n, fun h => h.nat_sub n⟩
#align irrational_nat_sub_iff irrational_nat_sub_iff

@[simp]
theorem irrational_sub_rat_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_rat q, sub_rat q⟩
#align irrational_sub_rat_iff irrational_sub_rat_iff

@[simp]
theorem irrational_sub_int_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_int m, fun h => h.sub_int m⟩
#align irrational_sub_int_iff irrational_sub_int_iff

@[simp]
theorem irrational_sub_nat_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_nat n, fun h => h.sub_nat n⟩
#align irrational_sub_nat_iff irrational_sub_nat_iff

@[simp]
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩
#align irrational_neg_iff irrational_neg_iff

@[simp]
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩
#align irrational_inv_iff irrational_inv_iff

@[simp]
theorem irrational_rat_mul_iff : Irrational (q * x) ↔ q ≠ 0 ∧ Irrational x :=
  ⟨fun h => ⟨Rat.cast_ne_zero.1 <| left_ne_zero_of_mul h.ne_zero, h.of_rat_mul q⟩, fun h =>
    h.2.rat_mul h.1⟩
#align irrational_rat_mul_iff irrational_rat_mul_iff

@[simp]
theorem irrational_mul_rat_iff : Irrational (x * q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [mul_comm, irrational_rat_mul_iff]
#align irrational_mul_rat_iff irrational_mul_rat_iff

@[simp]
theorem irrational_int_mul_iff : Irrational (m * x) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_rat_mul_iff, Int.cast_ne_zero]
#align irrational_int_mul_iff irrational_int_mul_iff

@[simp]
theorem irrational_mul_int_iff : Irrational (x * m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_mul_rat_iff, Int.cast_ne_zero]
#align irrational_mul_int_iff irrational_mul_int_iff

@[simp]
theorem irrational_nat_mul_iff : Irrational (n * x) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_rat_mul_iff, Nat.cast_ne_zero]
#align irrational_nat_mul_iff irrational_nat_mul_iff

@[simp]
theorem irrational_mul_nat_iff : Irrational (x * n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_mul_rat_iff, Nat.cast_ne_zero]
#align irrational_mul_nat_iff irrational_mul_nat_iff

@[simp]
theorem irrational_rat_div_iff : Irrational (q / x) ↔ q ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_rat_div_iff irrational_rat_div_iff

@[simp]
theorem irrational_div_rat_iff : Irrational (x / q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [div_eq_mul_inv, ← cast_inv, irrational_mul_rat_iff, Ne, inv_eq_zero]
#align irrational_div_rat_iff irrational_div_rat_iff

@[simp]
theorem irrational_int_div_iff : Irrational (m / x) ↔ m ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_int_div_iff irrational_int_div_iff

@[simp]
theorem irrational_div_int_iff : Irrational (x / m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_intCast, irrational_div_rat_iff, Int.cast_ne_zero]
#align irrational_div_int_iff irrational_div_int_iff

@[simp]
theorem irrational_nat_div_iff : Irrational (n / x) ↔ n ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_nat_div_iff irrational_nat_div_iff

@[simp]
theorem irrational_div_nat_iff : Irrational (x / n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_natCast, irrational_div_rat_iff, Nat.cast_ne_zero]
#align irrational_div_nat_iff irrational_div_nat_iff

/-- There is an irrational number `r` between any two reals `x < r < y`. -/
theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.rat_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩
#align exists_irrational_btwn exists_irrational_btwn

end
