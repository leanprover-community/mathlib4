/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.invOneSubPow`: given a commutative ring `S` and a number `d : ℕ`,
  `PowerSeries.invOneSubPow d : S⟦X⟧ˣ` is the power series `∑ n, Nat.choose (d + n) d`
  whose multiplicative inverse is `(1 - X) ^ (d + 1)`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/


namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- The power series for `1 / (u - x)`. -/
def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)

@[simp]
theorem coeff_invUnitsSub (u : Rˣ) (n : ℕ) : coeff R n (invUnitsSub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff R (invUnitsSub u) = 1 /ₚ u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invUnitsSub, zero_add, pow_one]

@[simp]
theorem invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C R u - 1 := by
  ext (_ | n)
  · simp
  · simp [n.succ_ne_zero, pow_succ']

@[simp]
theorem invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C R u - X) = 1 := by
  simp [mul_sub, sub_sub_cancel]

theorem map_invUnitsSub (f : R →+* S) (u : Rˣ) :
    map f (invUnitsSub u) = invUnitsSub (Units.map (f : R →* S) u) := by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

end Ring

section invOneSubPow

variable {S : Type*} [CommRing S] (d : ℕ)

/--
(1 + X + X^2 + ...) * (1 - X) = 1.

Note that the power series `1 + X + X^2 + ...` is written as `mk 1` where `1` is the constant
function so that `mk 1` is the power series with all coefficients equal to one.
-/
theorem mk_one_mul_one_sub_eq_one : (mk 1 : S⟦X⟧) * (1 - X) = 1 := by
  rw [mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

/--
Note that `mk 1` is the constant function `1` so the power series `1 + X + X^2 + ...`. This theorem
states that for any `d : ℕ`, `(1 + X + X^2 + ... : S⟦X⟧) ^ (d + 1)` is equal to the power series
`mk fun n => Nat.choose (d + n) d : S⟦X⟧`.
-/
theorem mk_one_pow_eq_mk_choose_add :
    (mk 1 : S⟦X⟧) ^ (d + 1) = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add, hd, pow_one, mul_comm, coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add, ← Nat.choose_succ_succ, Nat.succ_eq_add_one,
        add_right_comm]

/--
The power series `mk fun n => Nat.choose (d + n) d`, whose multiplicative inverse is
`(1 - X) ^ (d + 1)`.
-/
noncomputable def invOneSubPow : S⟦X⟧ˣ where
  val := mk fun n => Nat.choose (d + n) d
  inv := (1 - X) ^ (d + 1)
  val_inv := by
    rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]
  inv_val := by
    rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]

theorem invOneSubPow_val_eq_mk_choose_add :
    (invOneSubPow d).val = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := rfl

theorem invOneSubPow_val_zero_eq_invUnitSub_one :
    (invOneSubPow 0).val = invUnitsSub (1 : Sˣ) := by
  simp [invOneSubPow, invUnitsSub]

/--
The theorem `PowerSeries.mk_one_mul_one_sub_eq_one` implies that `1 - X` is a unit in `S⟦X⟧`
whose inverse is the power series `1 + X + X^2 + ...`. This theorem states that for any `d : ℕ`,
`PowerSeries.invOneSubPow d` is equal to `(1 - X)⁻¹ ^ (d + 1)`.
-/
theorem invOneSubPow_eq_inv_one_sub_pow :
    invOneSubPow d = (Units.mkOfMulEqOne (1 - X) (mk 1 : S⟦X⟧)
    <| Eq.trans (mul_comm _ _) mk_one_mul_one_sub_eq_one)⁻¹ ^ (d + 1) := by
  rw [inv_pow]
  exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow d) <| by
    rw [← Units.val_eq_one, Units.val_mul, Units.val_pow_eq_pow_val]
    exact (invOneSubPow d).inv_val).symm

theorem invOneSubPow_inv_eq_one_sub_pow :
    (invOneSubPow d).inv = (1 - X : S⟦X⟧) ^ (d + 1) := rfl

end invOneSubPow

section Field

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

/-- Power series for the exponential function at zero. -/
def exp : PowerSeries A :=
  mk fun n => algebraMap ℚ A (1 / n !)

/-- Power series for the sine function at zero. -/
def sin : PowerSeries A :=
  mk fun n => if Even n then 0 else algebraMap ℚ A ((-1) ^ (n / 2) / n !)

/-- Power series for the cosine function at zero. -/
def cos : PowerSeries A :=
  mk fun n => if Even n then algebraMap ℚ A ((-1) ^ (n / 2) / n !) else 0

variable {A A'} [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A'] (n : ℕ) (f : A →+* A')

@[simp]
theorem coeff_exp : coeff A n (exp A) = algebraMap ℚ A (1 / n !) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_exp : constantCoeff A (exp A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exp]
  simp

@[simp]
theorem map_exp : map (f : A →+* A') (exp A) = exp A' := by
  ext
  simp

@[simp]
theorem map_sin : map f (sin A) = sin A' := by
  ext
  simp [sin, apply_ite f]

@[simp]
theorem map_cos : map f (cos A) = cos A' := by
  ext
  simp [cos, apply_ite f]

end Field

open RingHom

open Finset Nat

variable {A : Type*} [CommRing A]

/-- Shows that $e^{aX} * e^{bX} = e^{(a + b)X}$ -/
theorem exp_mul_exp_eq_exp_add [Algebra ℚ A] (a b : A) :
    rescale a (exp A) * rescale b (exp A) = rescale (a + b) (exp A) := by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    factorial, Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap ℚ A (1 / ↑x.factorial) * algebraMap ℚ A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap ℚ A) (1 / ↑n.factorial))
    by convert this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap ℚ A) (n.choose x), ← map_mul, ← map_mul]
  refine RingHom.congr_arg _ ?_
  rw [mul_one_div (↑(n.choose x) : ℚ), one_div_mul_one_div]
  symm
  rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial]
  · norm_cast
    rw [cast_div_charZero]
    apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]

/-- Shows that $e^{x} * e^{-x} = 1$ -/
theorem exp_mul_exp_neg_eq_one [Algebra ℚ A] : exp A * evalNegHom (exp A) = 1 := by
  convert exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp

/-- Shows that $(e^{X})^k = e^{kX}$. -/
theorem exp_pow_eq_rescale_exp [Algebra ℚ A] (k : ℕ) : exp A ^ k = rescale (k : A) (exp A) := by
  induction' k with k h
  · simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero, zero_eq,
      pow_zero (exp A), coe_comp]
  · simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
    id_apply, rescale_one] using pow_succ (exp A) k

/-- Shows that
$\sum_{k = 0}^{n - 1} (e^{X})^k = \sum_{p = 0}^{\infty} \sum_{k = 0}^{n - 1} \frac{k^p}{p!}X^p$. -/
theorem exp_pow_sum [Algebra ℚ A] (n : ℕ) :
    ((Finset.range n).sum fun k => exp A ^ k) =
      PowerSeries.mk fun p => (Finset.range n).sum
        fun k => (k ^ p : A) * algebraMap ℚ A p.factorial⁻¹ := by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, cast_pow, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, factorial, map_sum]

end PowerSeries
