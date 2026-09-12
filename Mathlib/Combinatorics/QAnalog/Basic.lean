/-
Copyright (c) 2026 Alessandro Iraci, Giovanni Paolini, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Giovanni Paolini, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# `q`-analogues: `q`-numbers, `q`-factorials and `q`-Pochhammer symbols

This file introduces the basic `q`-analogues of natural numbers.

Everything here is developed over a not necessarily commutative (semi)ring: the various
`q`-analogues are built out of powers of a single element `q`, and these commute with each other.
Accordingly the `q`-factorial and the `q`-Pochhammer symbol are defined by recursion (with the
factors accumulated in a fixed order), and reduce to the expected products in the commutative
case, see `qFactorial_eq_prod_range` and `qPochhammer_eq_prod_range`.  The `Commute.qNat_right`
family of lemmas records that anything commuting with `q` commutes with its `q`-analogues.

## Main definitions

* `qNat q n`, the `q`-analogue `[n]_q = 1 + q + ⋯ + q ^ (n - 1)` of the natural number `n`.
* `qFactorial q n`, the `q`-factorial `[n]_q! = [1]_q [2]_q ⋯ [n]_q`.
* `qPochhammer q a n`, the `q`-Pochhammer symbol `(a; q)_n = (1 - a)(1 - aq) ⋯ (1 - a q ^ (n-1))`.

## Main results

* `qNat_add`, `qNat_mul`: the `q`-analogues of `m + n` and `m * n`.
* `qNat_one_left`, `qFactorial_one_left`: at `q = 1` one recovers `n` and `n !`.
* `qNat_mul_one_sub`: `[n]_q (1 - q) = 1 - q ^ n`, the closed form of the geometric sum.
* `qPochhammer_self`: `(q; q)_n = (1 - q) ^ n [n]_q!`.

## Notation

The scoped notations `[n]_q`, `[n]_q !` and `[a; q]_n` for `qNat q n`, `qFactorial q n` and
`qPochhammer q a n` are available in the `QAnalog` scope.
-/

open Finset Nat

variable {R S : Type*}

/-! ### `q`-numbers -/

section Semiring
variable [Semiring R] (q : R) (m n : ℕ)

/-- The `q`-analogue `[n]_q = 1 + q + ⋯ + q ^ (n - 1)` of a natural number `n`. -/
def qNat (q : R) (n : ℕ) : R := ∑ i ∈ range n, q ^ i

@[inherit_doc qNat]
scoped[QAnalog] notation:max "[" n "]_" q:max => qNat q n

theorem qNat_eq_sum_range : qNat q n = ∑ i ∈ range n, q ^ i := rfl

@[simp] theorem qNat_zero : qNat q 0 = 0 := sum_range_zero _

@[simp] theorem qNat_one : qNat q 1 = 1 := by simp [qNat]

theorem qNat_two : qNat q 2 = 1 + q := by simp [qNat, sum_range_succ]

/-- The recursion `[n + 1]_q = [n]_q + q ^ n`. -/
theorem qNat_succ : qNat q (n + 1) = qNat q n + q ^ n := sum_range_succ _ _

/-- The recursion `[n + 1]_q = 1 + q [n]_q`. -/
theorem qNat_succ' : qNat q (n + 1) = 1 + q * qNat q n := by
  rw [qNat, sum_range_succ', pow_zero, qNat, mul_sum, add_comm]
  exact congrArg (1 + ·) (sum_congr rfl fun i _ => pow_succ' q i)

/-- Anything commuting with `q` commutes with `[n]_q`. -/
theorem Commute.qNat_right {q a : R} (h : Commute a q) (n : ℕ) : Commute a (qNat q n) :=
  Commute.sum_right _ _ _ fun i _ => h.pow_right i

/-- Anything commuting with `q` commutes with `[n]_q`. -/
theorem Commute.qNat_left {q a : R} (h : Commute q a) (n : ℕ) : Commute (qNat q n) a :=
  (h.symm.qNat_right n).symm

theorem qNat_commute : Commute q (qNat q n) := (Commute.refl q).qNat_right n

theorem qNat_commute_pow : Commute (q ^ m) (qNat q n) := ((Commute.refl q).pow_left m).qNat_right n

theorem qNat_commute_qNat : Commute (qNat q m) (qNat q n) := (qNat_commute q n).qNat_left m

/-- The `q`-analogue of `m + n`. -/
theorem qNat_add : qNat q (m + n) = qNat q m + q ^ m * qNat q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← add_assoc, qNat_succ, qNat_succ, ih, pow_add, add_assoc, mul_add]

/-- The `q`-analogue of `m * n`. -/
theorem qNat_mul : qNat q (m * n) = qNat q m * qNat (q ^ m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, qNat_add, ih, qNat_succ, mul_add, ← pow_mul,
      (qNat_commute_pow q (m * n) m).eq]

@[simp] theorem qNat_one_left : qNat (1 : R) n = n := by simp [qNat]

end Semiring

section Hom

/-- `q`-numbers commute with (semi)ring homomorphisms. -/
@[simp] theorem map_qNat {F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (q : R) (n : ℕ) : f (qNat q n) = qNat (f q) n := by
  simp [qNat, map_sum, map_pow]

end Hom

section Ring
variable [Ring R] (q : R) (n : ℕ)

/-- The closed form of the geometric sum: `[n]_q (1 - q) = 1 - q ^ n`. -/
theorem qNat_mul_one_sub : qNat q n * (1 - q) = 1 - q ^ n := geom_sum_mul_neg q n

/-- The closed form of the geometric sum: `(1 - q) [n]_q = 1 - q ^ n`. -/
theorem one_sub_mul_qNat : (1 - q) * qNat q n = 1 - q ^ n := mul_neg_geom_sum q n

end Ring

/-! ### `q`-factorials -/

section Semiring
variable [Semiring R] (q : R) (m n : ℕ)

/-- The `q`-factorial `[n]_q ! = [1]_q [2]_q ⋯ [n]_q`. -/
def qFactorial (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qNat q (n + 1) * qFactorial q n

@[inherit_doc qFactorial]
scoped[QAnalog] notation:max "[" n "]_" q:max "!" => qFactorial q n

@[simp] theorem qFactorial_zero : qFactorial q 0 = 1 := rfl

theorem qFactorial_succ : qFactorial q (n + 1) = qNat q (n + 1) * qFactorial q n := rfl

@[simp] theorem qFactorial_one : qFactorial q 1 = 1 := by simp [qFactorial_succ]

/-- Anything commuting with `q` commutes with `[n]_q !`. -/
theorem Commute.qFactorial_right {q a : R} (h : Commute a q) (n : ℕ) :
    Commute a (qFactorial q n) := by
  induction n with
  | zero => simp
  | succ n ih => exact (h.qNat_right (n + 1)).mul_right ih

/-- Anything commuting with `q` commutes with `[n]_q !`. -/
theorem Commute.qFactorial_left {q a : R} (h : Commute q a) (n : ℕ) :
    Commute (qFactorial q n) a := (h.symm.qFactorial_right n).symm

theorem qFactorial_commute : Commute q (qFactorial q n) := (Commute.refl q).qFactorial_right n

theorem qNat_commute_qFactorial : Commute (qNat q m) (qFactorial q n) :=
  (qFactorial_commute q n).qNat_left m

theorem qFactorial_commute_qFactorial : Commute (qFactorial q m) (qFactorial q n) :=
  (qFactorial_commute q n).qFactorial_left m

/-- The `q`-factorial as a product of `q`-numbers; the factors commute, so the order in which
they are multiplied is irrelevant. -/
theorem qFactorial_succ' : qFactorial q (n + 1) = qFactorial q n * qNat q (n + 1) :=
  (qFactorial_succ q n).trans (qNat_commute_qFactorial q (n + 1) n).eq

@[simp] theorem qFactorial_one_left : qFactorial (1 : R) n = n ! := by
  induction n with
  | zero => simp
  | succ n ih => rw [qFactorial_succ, ih, Nat.factorial_succ, qNat_one_left, Nat.cast_mul]

end Semiring

section CommSemiring
variable [CommSemiring R] (q : R) (n : ℕ)

theorem qFactorial_eq_prod_range : qFactorial q n = ∏ i ∈ range n, qNat q (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [qFactorial_succ', ih, prod_range_succ]

end CommSemiring

/-! ### `q`-Pochhammer symbols -/

section Ring
variable [Ring R] (q a : R) (n : ℕ)

/-- The `q`-Pochhammer symbol `(a; q)_n = (1 - a)(1 - aq) ⋯ (1 - a q ^ (n - 1))`. -/
def qPochhammer (q a : R) : ℕ → R
  | 0 => 1
  | n + 1 => qPochhammer q a n * (1 - a * q ^ n)

@[inherit_doc qPochhammer]
scoped[QAnalog] notation:max "[" a "; " q "]_" n:max => qPochhammer q a n

@[simp] theorem qPochhammer_zero : qPochhammer q a 0 = 1 := rfl

theorem qPochhammer_succ : qPochhammer q a (n + 1) = qPochhammer q a n * (1 - a * q ^ n) := rfl

/-- Peeling off the first factor: `(a; q)_{n+1} = (1 - a) (aq; q)_n`. -/
theorem qPochhammer_succ' : qPochhammer q a (n + 1) = (1 - a) * qPochhammer q (a * q) n := by
  induction n with
  | zero => simp [qPochhammer_succ]
  | succ n ih =>
    rw [qPochhammer_succ, ih, qPochhammer_succ, mul_assoc, pow_succ' q n, ← mul_assoc a q]

@[simp] theorem qPochhammer_one : qPochhammer q a 1 = 1 - a := by simp [qPochhammer_succ]

@[simp] theorem qPochhammer_zero_left : qPochhammer q 0 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qPochhammer_succ, ih]; simp

/-- `(q; q)_n = (1 - q) ^ n [n]_q !`. -/
theorem qPochhammer_self : qPochhammer q q n = (1 - q) ^ n * qFactorial q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (1 - q) (qFactorial q n) :=
      ((Commute.one_left q).sub_left (Commute.refl q)).qFactorial_right n
    rw [qPochhammer_succ, ih, ← pow_succ' q n, ← one_sub_mul_qNat, qFactorial_succ, pow_succ,
      mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← hc.eq, mul_assoc, ← (qNat_commute_qFactorial q (n + 1) n).eq]

end Ring

section CommRing
variable [CommRing R] (q a : R) (n : ℕ)

theorem qPochhammer_eq_prod_range : qPochhammer q a n = ∏ i ∈ range n, (1 - a * q ^ i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [qPochhammer_succ, ih, prod_range_succ]

end CommRing
