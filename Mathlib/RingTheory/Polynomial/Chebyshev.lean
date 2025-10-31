/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.LinearCombination

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
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/

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

@[simp]
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

@[simp]
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
    linear_combination (norm := ring_nf) (X:R[X]) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := C_add_one R n
    have h₂ := C_sub_one R (-n)
    linear_combination (norm := ring_nf) (X:R[X]) * ih1 - ih2 + h₁ - h₂

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
    linear_combination (norm := ring_nf) (X:R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_eq R n
    have h₂ := S_sub_two R (-n)
    linear_combination (norm := ring_nf) (X:R[X]) * ih1 - ih2 + h₁ + h₂

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
    linear_combination (norm := ring_nf) -h₃ - (X:R[X]) * h₂ + 2 * h₁ + (X:R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (-n - 1)
    have h₂ := S_add_two R (-n)
    have h₃ := C_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + 2 * h₂ - (X:R[X]) * h₁ - ih2 + (X:R[X]) * ih1

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
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X:R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := C_add_two R (m + (-k - 1))
    have h₂ := C_sub_two R (m - (-k - 1))
    have h₃ := C_add_two R (-k - 1)
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X:R[X]) * ih1

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
