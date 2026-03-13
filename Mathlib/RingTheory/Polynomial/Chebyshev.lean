/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Chebyshev polynomials

The Chebyshev polynomials are families of polynomials indexed by `ℤ`,
with integral coefficients.

## Main definitions

* `Polynomial.Chebyshev.T`: the Chebyshev polynomials of the first kind.
* `Polynomial.Chebyshev.U`: the Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.C`: the rescaled Chebyshev polynomials of the first kind (also known as the
  Vieta–Lucas polynomials), given by $C_n(2x) = 2T_n(x)$.
* `Polynomial.Chebyshev.S`: the rescaled Chebyshev polynomials of the second kind (also known as the
  Vieta–Fibonacci polynomials), given by $S_n(2x) = U_n(x)$.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.T_mul_T`, twice the product of the `m`-th and `k`-th Chebyshev polynomials
  of the first kind is the sum of the `m + k`-th and `m - k`-th Chebyshev polynomials of the first
  kind. There is a similar statement `Polynomial.Chebyshev.C_mul_C` for the `C` polynomials.
* `Polynomial.Chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind. There is a similar
  statement `Polynomial.Chebyshev.C_mul` for the `C` polynomials.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (Int.castRingHom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `LinearRecurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Polynomial

variable (R R' : Type*) [CommRing R] [CommRing R']

/-- `T n` is the `n`-th Chebyshev polynomial of the first kind. -/
noncomputable def T : ℤ → R[X]
  | 0 => 1
  | 1 => X
  | (n : ℕ) + 2 => 2 * X * T (n + 1) - T n
  | -((n : ℕ) + 1) => 2 * X * T (-n) - T (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

/-- Induction principle used for proving facts about Chebyshev polynomials. -/
@[elab_as_elim]
protected theorem induct (motive : ℤ → Prop)
    (zero : motive 0)
    (one : motive 1)
    (add_two : ∀ (n : ℕ), motive (↑n + 1) → motive ↑n → motive (↑n + 2))
    (neg_add_one : ∀ (n : ℕ), motive (-↑n) → motive (-↑n + 1) → motive (-↑n - 1)) :
    ∀ (a : ℤ), motive a :=
  T.induct motive zero one add_two fun n hn hnm => by
    simpa only [Int.negSucc_eq, neg_add] using neg_add_one n hn hnm

/-- Another induction principle used for proving facts about Chebyshev polynomials,
    which is sometimes easier to use -/
@[elab_as_elim]
protected theorem induct' (motive : ℤ → Prop)
    (zero : motive 0)
    (one : motive 1)
    (add_two : ∀ (n : ℕ), motive (↑n + 1) → motive ↑n → motive (↑n + 2))
    (neg : ∀ (n : ℤ), motive n → motive (-n)) :
    ∀ (a : ℤ), motive a := by
  refine Chebyshev.induct motive zero one add_two ?_
  have neg' (n : ℤ) (h : motive (-n)) : motive n := by
    convert neg (-n) h; rw [neg_neg]
  intro n h₀ h₁
  cases n with
  | zero => exact neg 1 h₁
  | succ n =>
    apply neg (n + 2) (add_two n (neg' _ h₀) (neg' n ?_))
    convert h₁ using 1; omega

@[simp]
theorem T_add_two : ∀ n, T R (n + 2) = 2 * X * T R (n + 1) - T R n
  | (k : ℕ) => T.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) T.eq_4 R k

theorem T_add_one (n : ℤ) : T R (n + 1) = 2 * X * T R n - T R (n - 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

theorem T_sub_two (n : ℤ) : T R (n - 2) = 2 * X * T R (n - 1) - T R n := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

theorem T_sub_one (n : ℤ) : T R (n - 1) = 2 * X * T R n - T R (n + 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

theorem T_eq (n : ℤ) : T R n = 2 * X * T R (n - 1) - T R (n - 2) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

@[simp]
theorem T_zero : T R 0 = 1 := by simp [T]

@[simp]
theorem T_one : T R 1 = X := by simp [T]

theorem T_neg_one : T R (-1) = X := by
  change T R (Int.negSucc 0) = X
  rw [T]
  suffices 2 * X - X = X by simpa
  ring


theorem T_two : T R 2 = 2 * X ^ 2 - 1 := by
  unfold T; simp [pow_two, mul_assoc]

@[simp]
theorem T_neg (n : ℤ) : T R (-n) = T R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [T_neg_one, T_one]
  | add_two n ih1 ih2 =>
    have h₁ := T_add_two R n
    have h₂ := T_sub_two R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := T_add_one R n
    have h₂ := T_sub_one R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 + h₁ - h₂

theorem T_natAbs (n : ℤ) : T R n.natAbs = T R n := by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

theorem T_neg_two : T R (-2) = 2 * X ^ 2 - 1 := by simp [T_two]

@[simp]
theorem T_eval_one (n : ℤ) : (T R n).eval 1 = 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [T_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [T_sub_one, -T_neg, ih1, ih2]; norm_num

set_option backward.isDefEq.respectTransparency false in
theorem T_eval_neg_one (n : ℤ) : (T R n).eval (-1) = n.negOnePow := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

theorem T_eval_zero (n : ℤ) :
    (T R n).eval 0 = (if Even n then (n / 2).negOnePow else 0 : ℤ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : ℤ) + 2) / 2 = (n : ℤ) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : ℤ) + 1) / 2 = (-(n : ℤ) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [T_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]
theorem T_eval_zero_of_even {n : ℤ} (hn : Even n) : (T R n).eval 0 = (n / 2).negOnePow := by
  simp [T_eval_zero, hn]

theorem T_eval_two_mul_zero (n : ℤ) : (T R (2 * n)).eval 0 = n.negOnePow := by simp

@[simp]
theorem T_eval_zero_of_odd {n : ℤ} (hn : Odd n) : (T R n).eval 0 = 0 := by
  simp [T_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]
theorem degree_T [IsDomain R] [NeZero (2 : R)] (n : ℤ) : (T R n).degree = n.natAbs := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : (2 * X * T R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, ih1]
      norm_cast
    rw [T_add_two, degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih2, this]; tauto
  | neg n ih => simp [ih]

@[simp]
theorem natDegree_T [IsDomain R] [NeZero (2 : R)] (n : ℤ) : (T R n).natDegree = n.natAbs :=
  natDegree_eq_of_degree_eq_some (degree_T R n)

@[simp]
theorem leadingCoeff_T [IsDomain R] [NeZero (2 : R)] (n : ℤ) :
    (T R n).leadingCoeff = 2 ^ (n.natAbs - 1) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : leadingCoeff (2 : R[X]) = 2 := by
      change leadingCoeff (C 2) = 2
      rw [leadingCoeff_C]
    rw [T_add_two, leadingCoeff_sub_of_degree_lt, leadingCoeff_mul, ih1,
      leadingCoeff_mul, leadingCoeff_X, this]
    · norm_cast; simp [pow_add, mul_comm]
    · rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, degree_T,
        degree_T]
      tauto
  | neg n ih => simp [ih]

@[simp]
theorem T_eval_neg (n : ℤ) (x : R) : (T R n).eval (-x) = n.negOnePow * (T R n).eval x := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    trans (n + 2 : ℤ).negOnePow * (2 * x * (T R (n + 1)).eval x - (T R n).eval x)
    · simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, ih1, Int.negOnePow_add,
        Int.negOnePow_one, Units.val_neg, Int.cast_neg, ih2, Int.negOnePow_even 2 even_two]
      ring_nf
    · simp
  | neg n ih => simp [ih]

theorem T_ne_zero (n : ℤ) [IsDomain R] [NeZero (2 : R)] : T R n ≠ 0 :=
  (T R n).degree_ne_bot.mp (by simp [degree_T R n])

/-- `U n` is the `n`-th Chebyshev polynomial of the second kind. -/
noncomputable def U : ℤ → R[X]
  | 0 => 1
  | 1 => 2 * X
  | (n : ℕ) + 2 => 2 * X * U (n + 1) - U n
  | -((n : ℕ) + 1) => 2 * X * U (-n) - U (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
theorem U_add_two : ∀ n, U R (n + 2) = 2 * X * U R (n + 1) - U R n
  | (k : ℕ) => U.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) U.eq_4 R k

theorem U_add_one (n : ℤ) : U R (n + 1) = 2 * X * U R n - U R (n - 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

theorem U_sub_two (n : ℤ) : U R (n - 2) = 2 * X * U R (n - 1) - U R n := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

theorem U_sub_one (n : ℤ) : U R (n - 1) = 2 * X * U R n - U R (n + 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

theorem U_eq (n : ℤ) : U R n = 2 * X * U R (n - 1) - U R (n - 2) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

@[simp]
theorem U_zero : U R 0 = 1 := by simp [U]

@[simp]
theorem U_one : U R 1 = 2 * X := by simp [U]

@[simp]
theorem U_neg_one : U R (-1) = 0 := by simpa using U_sub_one R 0

theorem U_two : U R 2 = 4 * X ^ 2 - 1 := by
  have := U_add_two R 0
  simp only [zero_add, U_one, U_zero] at this
  linear_combination this

@[simp]
theorem U_neg_two : U R (-2) = -1 := by
  simpa [zero_sub, Int.reduceNeg, U_neg_one, mul_zero, U_zero] using U_sub_two R 0

theorem U_neg_sub_one (n : ℤ) : U R (-n - 1) = -U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := U_add_one R n
    have h₂ := U_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_eq R n
    have h₂ := U_sub_two R (-n)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂

theorem U_neg (n : ℤ) : U R (-n) = -U R (n - 2) := by simpa [sub_sub] using U_neg_sub_one R (n - 1)

@[simp]
theorem U_neg_sub_two (n : ℤ) : U R (-n - 2) = -U R n := by
  simpa [sub_eq_add_neg, add_comm] using U_neg R (n + 2)

@[simp]
theorem U_eval_one (n : ℤ) : (U R n).eval 1 = n + 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

set_option backward.isDefEq.respectTransparency false in
theorem U_eval_neg_one (n : ℤ) : (U R n).eval (-1) = n.negOnePow * (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

theorem U_eval_zero (n : ℤ) :
    (U R n).eval 0 = (if Even n then (n / 2).negOnePow else 0 : ℤ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : ℤ) + 2) / 2 = (n : ℤ) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : ℤ) + 1) / 2 = (-(n : ℤ) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [U_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]
theorem U_eval_zero_of_even {n : ℤ} (hn : Even n) : (U R n).eval 0 = (n / 2).negOnePow := by
  simp [U_eval_zero, hn]

theorem U_eval_two_mul_zero (n : ℤ) : (U R (2 * n)).eval 0 = n.negOnePow := by simp

@[simp]
theorem U_eval_zero_of_odd {n : ℤ} (hn : Odd n) : (U R n).eval 0 = 0 := by
  simp [U_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]
theorem degree_U_natCast [IsDomain R] [NeZero (2 : R)] (n : ℕ) : (U R n).degree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_cast
    rw [U_one, ← C_ofNat, degree_C_mul_X two_ne_zero]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    have : (2 * X * U R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, ih2]
      norm_cast
    rw [U_add_two, degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih1, this]; norm_cast; omega

@[simp]
theorem natDegree_U_natCast [IsDomain R] [NeZero (2 : R)] (n : ℕ) : (U R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_U_natCast R n)

theorem degree_U_neg_one : (U R (-1)).degree = ⊥ := by simp

theorem natDegree_U_neg_one : (U R (-1)).natDegree = 0 := by simp

theorem degree_U_of_ne_neg_one [IsDomain R] [NeZero (2 : R)] (n : ℤ) (hn : n ≠ -1) :
    (U R n).degree = ↑((n + 1).natAbs - 1) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  case inl => rw [degree_U_natCast R m]; norm_cast
  case inr =>
    rw [U_neg, degree_neg]
    cases m with
    | zero => simp
    | succ m =>
      cases m with
      | zero => contradiction
      | succ m =>
        trans (U R m).degree
        · congr; omega
        · rw [degree_U_natCast R m]; norm_cast

theorem natDegree_U [IsDomain R] [NeZero (2 : R)] (n : ℤ) :
    (U R n).natDegree = (n + 1).natAbs - 1 := by
  by_cases n = -1
  case pos hn => subst hn; simp
  case neg hn => exact natDegree_eq_of_degree_eq_some (degree_U_of_ne_neg_one R n hn)

@[simp]
theorem leadingCoeff_U_natCast [IsDomain R] [NeZero (2 : R)] (n : ℕ) :
    (U R n).leadingCoeff = 2 ^ n := by
  have : leadingCoeff (2 : R[X]) = 2 := by
    rw [← C_ofNat, leadingCoeff_C]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [this]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    rw [U_add_two, leadingCoeff_sub_of_degree_lt, leadingCoeff_mul, ih2,
      leadingCoeff_mul, leadingCoeff_X, this]
    · norm_cast; rw [pow_add, pow_add]; ring_nf
    · norm_cast
      rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X,
        degree_U_natCast R n, degree_U_natCast R (n + 1)]
      norm_cast; omega

@[simp]
theorem U_eval_neg (n : ℕ) (x : R) : (U R n).eval (-x) = (n : ℤ).negOnePow * (U R n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    trans (n + 2 : ℤ).negOnePow * (2 * x * (U R (n + 1)).eval x - (U R n).eval x)
    · push_cast; push_cast at ih2
      rw [U_add_two, eval_sub, eval_mul, eval_mul, ih1, ih2,
        Int.negOnePow_succ, Int.negOnePow_add, Int.negOnePow_even 2 even_two]
      simp; ring
    · simp

theorem U_ne_zero (n : ℤ) [IsDomain R] [NeZero (2 : R)] (hn : n ≠ -1) : U R n ≠ 0 :=
  (U R n).degree_ne_bot.mp (by simp [degree_U_of_ne_neg_one R n hn])

theorem U_eq_zero_iff (n : ℤ) [IsDomain R] [NeZero (2 : R)] :
    U R n = 0 ↔ n = -1 :=
  ⟨fun h => by contrapose! h; exact U_ne_zero R n h, fun h => by simp [h]⟩

theorem U_eq_X_mul_U_add_T (n : ℤ) : U R (n + 1) = X * U R n + T R (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [U_two, T_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + h₁ + 2 * (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_add_two R (-n - 1)
    have h₂ := U_add_two R (-n)
    have h₃ := T_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + h₂ - (X : R[X]) * h₁ - ih2 + 2 * (X : R[X]) * ih1

theorem T_eq_U_sub_X_mul_U (n : ℤ) : T R n = U R n - X * U R (n - 1) := by
  linear_combination (norm := ring_nf) - U_eq_X_mul_U_add_T R (n - 1)

theorem T_eq_X_mul_T_sub_pol_U (n : ℤ) : T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n := by
  have h₁ := U_eq_X_mul_U_add_T R n
  have h₂ := U_eq_X_mul_U_add_T R (n + 1)
  have h₃ := U_add_two R n
  linear_combination (norm := ring_nf) h₃ - h₂ + (X : R[X]) * h₁

theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : ℤ) :
    (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2) := by
  linear_combination T_eq_X_mul_T_sub_pol_U R n

theorem T_eq_X_mul_U_sub_U (n : ℤ) : T R (n + 2) = X * U R (n + 1) - U R n := by
  have h := T_eq_U_sub_X_mul_U (R := R) (-(n + 2))
  rw [T_neg, U_neg, Int.add_sub_cancel, ← neg_add' _ 1, U_neg,
    show n + 2 + 1 - 2 = n + 1 by ring] at h
  linear_combination (norm := ring_nf) h

theorem two_mul_T_eq_U_sub_U (n : ℤ) : 2 * T R (n + 2) = U R (n + 2) - U R n := by
  linear_combination (norm := ring_nf) (T_eq_U_sub_X_mul_U R (n + 2)) + (T_eq_X_mul_U_sub_U R n)

theorem U_eq_two_mul_T_add_U (n : ℤ) : U R (n + 2) = 2 * T R (n + 2) + U R n := by
  linear_combination (norm := ring_nf) - (two_mul_T_eq_U_sub_U R n)

theorem U_mem_span_T (n : ℕ) : U R n ∈ Submodule.span ℕ ((fun m : ℕ => T R m) '' Set.Icc 0 n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [show U R (1 : ℕ) = 2 * T R 1 by simp, ← smul_eq_mul]; norm_cast
    exact Submodule.smul_of_tower_mem _ 2 (Submodule.mem_span_of_mem ⟨1, by simp⟩)
  | more n h₀ _ =>
    push_cast; rw [U_eq_two_mul_T_add_U, ← smul_eq_mul]; norm_cast
    refine Submodule.add_mem _ ?_ ((Submodule.span_mono (by grind)) h₀)
    · exact Submodule.smul_of_tower_mem _ 2
        (Submodule.mem_span_of_mem ⟨n + 2, by simp⟩)

/-- `C n` is the `n`th rescaled Chebyshev polynomial of the first kind (also known as a Vieta–Lucas
polynomial), given by $C_n(2x) = 2T_n(x)$. See `Polynomial.Chebyshev.C_comp_two_mul_X`. -/
noncomputable def C : ℤ → R[X]
  | 0 => 2
  | 1 => X
  | (n : ℕ) + 2 => X * C (n + 1) - C n
  | -((n : ℕ) + 1) => X * C (-n) - C (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
theorem C_add_two : ∀ n, C R (n + 2) = X * C R (n + 1) - C R n
  | (k : ℕ) => C.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) C.eq_4 R k

theorem C_add_one (n : ℤ) : C R (n + 1) = X * C R n - C R (n - 1) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

theorem C_sub_two (n : ℤ) : C R (n - 2) = X * C R (n - 1) - C R n := by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

theorem C_sub_one (n : ℤ) : C R (n - 1) = X * C R n - C R (n + 1) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

theorem C_eq (n : ℤ) : C R n = X * C R (n - 1) - C R (n - 2) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

@[simp]
theorem C_zero : C R 0 = 2 := by simp [C]

@[simp]
theorem C_one : C R 1 = X := by simp [C]

theorem C_neg_one : C R (-1) = X := by
  change C R (Int.negSucc 0) = X
  rw [C]
  suffices X * 2 - X = X by simpa
  ring

theorem C_two : C R 2 = X ^ 2 - 2 := by
  simpa [pow_two, mul_assoc] using C_add_two R 0

@[simp]
theorem C_neg (n : ℤ) : C R (-n) = C R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [C_neg_one, C_one]
  | add_two n ih1 ih2 =>
    have h₁ := C_add_two R n
    have h₂ := C_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := C_add_one R n
    have h₂ := C_sub_one R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ - h₂

theorem C_natAbs (n : ℤ) : C R n.natAbs = C R n := by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

theorem C_neg_two : C R (-2) = X ^ 2 - 2 := by simp [C_two]

theorem C_comp_two_mul_X (n : ℤ) : (C R n).comp (2 * X) = 2 * T R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, T_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, T_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring

@[simp]
theorem C_eval_two (n : ℤ) : (C R n).eval 2 = 2 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [C_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [C_sub_one, -C_neg, ih1, ih2]; norm_num

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem C_eval_neg_two (n : ℤ) : (C R n).eval (-2) = 2 * n.negOnePow := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [C_add_two, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [C_sub_one, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

theorem C_eq_two_mul_T_comp_half_mul_X [Invertible (2 : R)] (n : ℤ) :
    C R n = 2 * (T R n).comp (Polynomial.C ⅟2 * X) := by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (C_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X, map_ofNat] at this
  assumption

theorem T_eq_half_mul_C_comp_two_mul_X [Invertible (2 : R)] (n : ℤ) :
    T R n = Polynomial.C ⅟2 * (C R n).comp (2 * X) := by
  rw [C_comp_two_mul_X, ← mul_assoc, ← map_ofNat Polynomial.C 2, ← map_mul, invOf_mul_self',
    map_one, one_mul]

/-- `S n` is the `n`th rescaled Chebyshev polynomial of the second kind (also known as a
Vieta–Fibonacci polynomial), given by $S_n(2x) = U_n(x)$. See
`Polynomial.Chebyshev.S_comp_two_mul_X`. -/
noncomputable def S : ℤ → R[X]
  | 0 => 1
  | 1 => X
  | (n : ℕ) + 2 => X * S (n + 1) - S n
  | -((n : ℕ) + 1) => X * S (-n) - S (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
theorem S_add_two : ∀ n, S R (n + 2) = X * S R (n + 1) - S R n
  | (k : ℕ) => S.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) S.eq_4 R k

theorem S_add_one (n : ℤ) : S R (n + 1) = X * S R n - S R (n - 1) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

theorem S_sub_two (n : ℤ) : S R (n - 2) = X * S R (n - 1) - S R n := by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

theorem S_sub_one (n : ℤ) : S R (n - 1) = X * S R n - S R (n + 1) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

theorem S_eq (n : ℤ) : S R n = X * S R (n - 1) - S R (n - 2) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

@[simp]
theorem S_zero : S R 0 = 1 := by simp [S]

@[simp]
theorem S_one : S R 1 = X := by simp [S]

@[simp]
theorem S_neg_one : S R (-1) = 0 := by simpa using S_sub_one R 0

theorem S_two : S R 2 = X ^ 2 - 1 := by
  have := S_add_two R 0
  simp only [zero_add, S_one, S_zero] at this
  linear_combination this

@[simp]
theorem S_neg_two : S R (-2) = -1 := by
  simpa [zero_sub, Int.reduceNeg, S_neg_one, mul_zero, S_zero] using S_sub_two R 0

theorem S_neg_sub_one (n : ℤ) : S R (-n - 1) = -S R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := S_add_one R n
    have h₂ := S_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_eq R n
    have h₂ := S_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂

theorem S_neg (n : ℤ) : S R (-n) = -S R (n - 2) := by simpa [sub_sub] using S_neg_sub_one R (n - 1)

@[simp]
theorem S_neg_sub_two (n : ℤ) : S R (-n - 2) = -S R n := by
  simpa [sub_eq_add_neg, add_comm] using S_neg R (n + 2)

@[simp]
theorem S_eval_two (n : ℤ) : (S R n).eval 2 = n + 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem S_eval_neg_two (n : ℤ) : (S R n).eval (-2) = n.negOnePow * (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X, mul_neg, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

theorem S_comp_two_mul_X (n : ℤ) : (S R n).comp (2 * X) = U R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp_rw [U_add_two, S_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
  | neg_add_one n ih1 ih2 => simp_rw [U_sub_one, S_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]

theorem S_sq_add_S_sq (n : ℤ) : S R n ^ 2 + S R (n + 1) ^ 2 - X * S R n * S R (n + 1) = 1 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have h₁ := S_add_two R n
    linear_combination (norm := ring_nf) (S R (2 + n) - S R n) * h₁ + ih
  | pred n ih =>
    have h₁ := S_sub_one R (-n)
    linear_combination (norm := ring_nf) (S R (-1 - n) - S R (1 - n)) * h₁ + ih

theorem S_eq_U_comp_half_mul_X [Invertible (2 : R)] (n : ℤ) :
    S R n = (U R n).comp (Polynomial.C ⅟2 * X) := by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (S_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X] at this
  assumption

theorem S_eq_X_mul_S_add_C (n : ℤ) : 2 * S R (n + 1) = X * S R n + C R (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [S_two, C_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := S_add_two R (n + 1)
    have h₂ := S_add_two R n
    have h₃ := C_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + 2 * h₁ + (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (-n - 1)
    have h₂ := S_add_two R (-n)
    have h₃ := C_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + 2 * h₂ - (X : R[X]) * h₁ - ih2 + (X : R[X]) * ih1

theorem C_eq_S_sub_X_mul_S (n : ℤ) : C R n = 2 * S R n - X * S R (n - 1) := by
  linear_combination (norm := ring_nf) - S_eq_X_mul_S_add_C R (n - 1)

variable {R R'}

@[simp]
theorem map_T (f : R →+* R') (n : ℤ) : map f (T R n) = T R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [T_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [T_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]
theorem map_U (f : R →+* R') (n : ℤ) : map f (U R n) = U R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [U_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [U_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]
theorem map_C (f : R →+* R') (n : ℤ) : map f (C R n) = C R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]
theorem map_S (f : R →+* R') (n : ℤ) : map f (S R n) = S R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [S_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [S_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]
theorem aeval_T [Algebra R R'] (x : R') (n : ℤ) : aeval x (T R n) = (T R' n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]

@[simp]
theorem aeval_U [Algebra R R'] (x : R') (n : ℤ) : aeval x (U R n) = (U R' n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]

@[simp]
theorem aeval_C [Algebra R R'] (x : R') (n : ℤ) : aeval x (C R n) = (C R' n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_C]

@[simp]
theorem aeval_S [Algebra R R'] (x : R') (n : ℤ) : aeval x (S R n) = (S R' n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_S]

@[simp]
theorem algebraMap_eval_T [Algebra R R'] (x : R) (n : ℤ) :
    algebraMap R R' ((T R n).eval x) = (T R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_T]

@[simp]
theorem algebraMap_eval_U [Algebra R R'] (x : R) (n : ℤ) :
    algebraMap R R' ((U R n).eval x) = (U R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_U]

@[simp]
theorem algebraMap_eval_C [Algebra R R'] (x : R) (n : ℤ) :
    algebraMap R R' ((C R n).eval x) = (C R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_C]

@[simp]
theorem algebraMap_eval_S [Algebra R R'] (x : R) (n : ℤ) :
    algebraMap R R' ((S R n).eval x) = (S R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_S]

theorem T_derivative_eq_U (n : ℤ) : derivative (T R n) = n * U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_add_two R n)
    have h₂ := U_sub_one R n
    have h₃ := T_eq_U_sub_X_mul_U R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + 2 * (X : R[X]) * ih1 + 2 * h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_sub_one R (-n))
    have h₂ := U_sub_two R (-n)
    have h₃ := T_eq_U_sub_X_mul_U R (-n)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + 2 * (X : R[X]) * ih1 + h₁ + 2 * h₃ + (n + 1) * h₂

theorem T_derivative_mem_span_T (n : ℕ) :
    derivative (T R n) ∈ Submodule.span ℕ ((fun m : ℕ => T R m) '' Set.Ico 0 n) := by
  by_cases! hn : n = 0
  · simp [hn]
  rw [T_derivative_eq_U, ← smul_eq_mul]; norm_cast
  refine Submodule.smul_of_tower_mem _ n ?_
  convert U_mem_span_T R (n - 1) using 2 <;> grind

theorem T_iterate_derivative_mem_span_T (n k : ℕ) :
    derivative^[k] (T R n) ∈ Submodule.span ℕ ((fun m : ℕ => T R m) '' Set.Icc 0 (n - k)) := by
  induction k
  case zero =>
    rw [Function.iterate_zero_apply]
    exact Submodule.mem_span_of_mem ⟨n, by simp⟩
  case succ k ih =>
    rw [Function.iterate_succ_apply']
    suffices Submodule.span ℕ ((fun m : ℕ => derivative (T R m)) '' Set.Icc 0 (n - k)) ≤
      Submodule.span ℕ ((fun m : ℕ => T R m) '' Set.Icc 0 (n - (k + 1))) by
      apply this
      convert Submodule.apply_mem_span_image_of_mem_span (derivative.restrictScalars ℕ) ih using 2
      simp [Set.image]
    refine Submodule.span_le.mpr (fun x hx => ?_)
    obtain ⟨m, hm, rfl⟩ := hx
    refine (Submodule.span_mono (by grind)) (T_derivative_mem_span_T (R := R) m)

theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : ℤ) :
    (1 - X ^ 2) * derivative (T R (n + 1)) = (n + 1 : R[X]) * (T R n - X * T R (n + 1)) := by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) (n + 1)
  have h₁ := T_add_two R n
  linear_combination (norm := (push_cast; ring_nf))
    (-n - 1) * h₁ + (-(X : R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁

theorem add_one_mul_T_eq_poly_in_U (n : ℤ) :
    ((n : R[X]) + 1) * T R (n + 1) = X * U R n - (1 - X ^ 2) * derivative (U R n) := by
  have h₁ := congr_arg derivative <| T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R (n + 1)
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + (n + 2) * h₂

theorem add_one_mul_self_mul_T_eq_poly_in_T (n : ℤ) :
    ((n + 1) * n : R[X]) * (T R (n + 1)) =
    (n : R[X]) * X * derivative (T R (n + 1)) - (n + 1 : R[X]) * derivative (T R n) := by
  have h := T_eq_X_mul_U_sub_U (R := R) (n - 1)
  rw [T_derivative_eq_U, T_derivative_eq_U]
  linear_combination (norm := (push_cast; ring_nf))
    (n + 1) * n * h

theorem one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (n : ℤ) :
    (1 - X ^ 2) * derivative^[2] (T R n) = X * derivative (T R n) - (n ^ 2 : R[X]) * T R n := by
  have h₁ := congr_arg derivative <| one_sub_X_sq_mul_derivative_T_eq_poly_in_T (R := R) (n - 1)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    C_eq_natCast, sub_add_cancel, Int.cast_sub, Int.cast_one, derivative_intCast] at h₁
  have h₂ := add_one_mul_self_mul_T_eq_poly_in_T (R := R) (n - 1)
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + h₂

theorem one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (n : ℤ) :
    (1 - X ^ 2) * derivative^[2] (U R n) =
      3 * X * derivative (U R n) - ((n + 2) * n : R[X]) * U R n := by
  have h := congr_arg derivative <| add_one_mul_T_eq_poly_in_U (R := R) n
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_one,
    derivative_X_pow, derivative_intCast, C_eq_natCast, T_derivative_eq_U] at h
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf)) h

theorem one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T (n : ℤ) (k : ℕ) :
    (1 - X ^ 2) * derivative^[k + 2] (T R n) =
      (2 * k + 1 : R[X]) * X * derivative^[k + 1] (T R n) -
      (n ^ 2 - k ^ 2 : R[X]) * derivative^[k] (T R n) := by
  have h := congr_arg derivative^[k] <| one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
    (R := R) n
  norm_cast at h
  rw [sub_mul, iterate_derivative_sub, one_mul, ← Function.iterate_add_apply, mul_comm (X ^ 2),
    iterate_derivative_sub, mul_comm X, iterate_derivative_intCast_mul,
    iterate_derivative_derivative_mul_X_sq, iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

theorem one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U (n : ℤ) (k : ℕ) :
    (1 - X ^ 2) * derivative^[k + 2] (U R n) =
      (2 * k + 3 : R[X]) * X * derivative^[k + 1] (U R n) -
      ((n + 1) ^ 2 - (k + 1) ^ 2 : R[X]) * derivative^[k] (U R n) := by
  have h := congr_arg derivative^[k] <| one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
    (R := R) n
  norm_cast at h
  rw [sub_mul, iterate_derivative_sub, one_mul, ← Function.iterate_add_apply, mul_comm (X ^ 2),
    iterate_derivative_sub, mul_assoc 3, ← Nat.cast_three, iterate_derivative_natCast_mul,
    mul_comm X, iterate_derivative_intCast_mul, iterate_derivative_derivative_mul_X_sq,
    iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

theorem one_sub_X_sq_mul_iterate_derivative_T_eval (n : ℤ) (k : ℕ) (x : R) :
    (1 - x ^ 2) * (derivative^[k + 2] (T R n)).eval x =
      (2 * k + 1) * x * (derivative^[k + 1] (T R n)).eval x -
      (n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval x := by
  have h := congr_arg (fun (p : R[X]) => p.eval x) <|
    one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

theorem one_sub_X_sq_mul_iterate_derivative_U_eval (n : ℤ) (k : ℕ) (x : R) :
    (1 - x ^ 2) * (derivative^[k + 2] (U R n)).eval x =
      (2 * k + 3) * x * (derivative^[k + 1] (U R n)).eval x -
      ((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval x := by
  have h := congr_arg (fun (p : R[X]) => p.eval x) <|
    one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

theorem iterate_derivative_T_eval_one_recurrence (n : ℤ) (k : ℕ) :
    (2 * k + 1) * (derivative^[k + 1] (T R n)).eval 1 =
      (n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval 1 := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 1
  rw [one_pow, sub_self, zero_mul, mul_one] at h
  exact sub_eq_zero.mp h.symm

theorem iterate_derivative_U_eval_one_recurrence (n : ℤ) (k : ℕ) :
    (2 * k + 3) * (derivative^[k + 1] (U R n)).eval 1 =
      ((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval 1 := by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 1
  rw [one_pow, sub_self, zero_mul, mul_one] at h
  exact sub_eq_zero.mp h.symm

theorem iterate_derivative_T_eval_zero_recurrence (n : ℤ) (k : ℕ) :
    (derivative^[k + 2] (T R n)).eval 0 =
      -(n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval 0 := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 0
  rw [zero_pow two_ne_zero, sub_zero, one_mul, mul_zero, zero_mul, zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

theorem iterate_derivative_U_eval_zero_recurrence (n : ℤ) (k : ℕ) :
    (derivative^[k + 2] (U R n)).eval 0 =
      -((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval 0 := by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 0
  rw [zero_pow two_ne_zero, sub_zero, one_mul, mul_zero, zero_mul, zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

theorem iterate_derivative_T_eval_one (n : ℤ) (k : ℕ) :
    (∏ l ∈ Finset.range k, (2 * l + 1)) * (derivative^[k] (T R n)).eval 1 =
      ∏ l ∈ Finset.range k, (n ^ 2 - l ^ 2) := by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self, mul_comm (2 * _ + 1),
      mul_assoc, iterate_derivative_T_eval_one_recurrence, ← mul_assoc, mul_comm _ (_ ^ 2 - _ ^ 2),
      mul_assoc, ih, Finset.prod_insert Finset.notMem_range_self]

theorem iterate_derivative_U_eval_one (n : ℤ) (k : ℕ) :
    (∏ l ∈ Finset.range k, (2 * l + 3)) * (derivative^[k] (U R n)).eval 1 =
      (∏ l ∈ Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2 : ℤ)) * (n + 1) := by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self, mul_comm (2 * _ + 3),
      mul_assoc, iterate_derivative_U_eval_one_recurrence, ← mul_assoc, mul_comm _ (_ ^ 2 - _ ^ 2),
      mul_assoc, ih, Finset.prod_insert Finset.notMem_range_self, mul_assoc]

theorem derivative_T_eval_one (n : ℤ) :
    (derivative (T R n)).eval 1 = n ^ 2 := by
  simp [T_derivative_eq_U, sq]

theorem derivative_U_eval_one (n : ℤ) :
    3 * (derivative (U R n)).eval 1 = (n + 2) * (n + 1) * n := by
  have h := iterate_derivative_U_eval_one (R := R) n 1
  simp only [Finset.range_one, Finset.prod_singleton, Function.iterate_one] at h
  grind

variable {𝔽 : Type*} [Field 𝔽]

theorem iterate_derivative_T_eval_one_eq_div [CharZero 𝔽] (n : ℤ) (k : ℕ) :
    (derivative^[k] (T 𝔽 n)).eval 1 =
      (∏ l ∈ Finset.range k, (n ^ 2 - l ^ 2)) / (∏ l ∈ Finset.range k, (2 * l + 1)) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity))),
    mul_comm, iterate_derivative_T_eval_one]

theorem iterate_derivative_U_eval_one_eq_div [CharZero 𝔽] (n : ℤ) (k : ℕ) :
    (derivative^[k] (U 𝔽 n)).eval 1 =
      ((∏ l ∈ Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2) : ℤ) * (n + 1)) /
      (∏ l ∈ Finset.range k, (2 * l + 3)) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity))),
    mul_comm, iterate_derivative_U_eval_one]

theorem iterate_derivative_T_eval_one_dvd (n : ℤ) (k : ℕ) :
    ((∏ l ∈ Finset.range k, (2 * l + 1) : ℕ) : 𝔽) ∣ (∏ l ∈ Finset.range k, (n ^ 2 - l ^ 2) : ℤ) :=
  dvd_of_mul_right_eq _ <| iterate_derivative_T_eval_one n k

theorem iterate_derivative_U_eval_one_dvd (n : ℤ) (k : ℕ) :
    ((∏ l ∈ Finset.range k, (2 * l + 3) : ℕ) : 𝔽) ∣
      ((∏ l ∈ Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2) : ℤ) * (n + 1)) :=
  dvd_of_mul_right_eq _ <| iterate_derivative_U_eval_one n k

theorem derivative_U_eval_one_eq_div [neZero3 : NeZero (3 : 𝔽)] (n : ℤ) :
    (derivative (U 𝔽 n)).eval 1 = ((n + 2) * (n + 1) * n) / 3 :=
  eq_div_of_mul_eq neZero3.ne ((mul_comm ..).trans (derivative_U_eval_one n))

theorem derivative_U_eval_one_dvd (n : ℤ) :
    (3 : 𝔽) ∣ (n + 2) * (n + 1) * n :=
  dvd_of_mul_right_eq _ (derivative_U_eval_one n)

variable (R)

/-- Twice the product of two Chebyshev `T` polynomials is the sum of two other Chebyshev `T`
polynomials. -/
theorem T_mul_T (m k : ℤ) : 2 * T R m * T R k = T R (m + k) + T R (m - k) := by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [T_add_one, T_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := T_add_two R (m + k)
    have h₂ := T_sub_two R (m - k)
    have h₃ := T_add_two R k
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := T_add_two R (m + (-k - 1))
    have h₂ := T_sub_two R (m - (-k - 1))
    have h₃ := T_add_two R (-k - 1)
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1

/-- The product of two Chebyshev `C` polynomials is the sum of two other Chebyshev `C` polynomials.
-/
theorem C_mul_C (m k : ℤ) : C R m * C R k = C R (m + k) + C R (m - k) := by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [mul_two]
  | one => rw [C_add_one, C_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := C_add_two R (m + k)
    have h₂ := C_sub_two R (m - k)
    have h₃ := C_add_two R k
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := C_add_two R (m + (-k - 1))
    have h₂ := C_sub_two R (m - (-k - 1))
    have h₃ := C_add_two R (-k - 1)
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1

/-- The `(m * n)`-th Chebyshev `T` polynomial is the composition of the `m`-th and `n`-th. -/
theorem T_mul (m n : ℤ) : T R (m * n) = (T R m).comp (T R n) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := T_mul_T R ((m + 1) * n) n
    have h₂ := congr_arg (comp · (T R n)) <| T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := T_mul_T R ((-m) * n) n
    have h₂ := congr_arg (comp · (T R n)) <| T_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1

/-- The `(m * n)`-th Chebyshev `C` polynomial is the composition of the `m`-th and `n`-th. -/
theorem C_mul (m n : ℤ) : C R (m * n) = (C R m).comp (C R n) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := C_mul_C R ((m + 1) * n) n
    have h₂ := congr_arg (comp · (C R n)) <| C_add_two R m
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := C_mul_C R ((-m) * n) n
    have h₂ := congr_arg (comp · (C R n)) <| C_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1

end Polynomial.Chebyshev
