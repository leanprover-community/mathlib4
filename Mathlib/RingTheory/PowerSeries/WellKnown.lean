/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

#align_import ring_theory.power_series.well_known from "leanprover-community/mathlib"@"8199f6717c150a7fe91c4534175f4cf99725978f"

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.invOneSubPow`: given a commutative ring `S` and a natural number `d`,
  `PowerSeries.invOneSubPow d : S⟦X⟧ˣ` is the series for `1 / ((1 - X) ^ (d + 1))`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/


namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- The power series for `1 / (u - x)`. -/
def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)
#align power_series.inv_units_sub PowerSeries.invUnitsSub

@[simp]
theorem coeff_invUnitsSub (u : Rˣ) (n : ℕ) : coeff R n (invUnitsSub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk _ _
#align power_series.coeff_inv_units_sub PowerSeries.coeff_invUnitsSub

@[simp]
theorem constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff R (invUnitsSub u) = 1 /ₚ u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invUnitsSub, zero_add, pow_one]
#align power_series.constant_coeff_inv_units_sub PowerSeries.constantCoeff_invUnitsSub

@[simp]
theorem invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C R u - 1 := by
  ext (_ | n)
  · simp
  · simp [n.succ_ne_zero, pow_succ]
set_option linter.uppercaseLean3 false in
#align power_series.inv_units_sub_mul_X PowerSeries.invUnitsSub_mul_X

@[simp]
theorem invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C R u - X) = 1 := by
  simp [mul_sub, sub_sub_cancel]
#align power_series.inv_units_sub_mul_sub PowerSeries.invUnitsSub_mul_sub

theorem map_invUnitsSub (f : R →+* S) (u : Rˣ) :
    map f (invUnitsSub u) = invUnitsSub (Units.map (f : R →* S) u) := by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

#align power_series.map_inv_units_sub PowerSeries.map_invUnitsSub

section invOneSubPow

variable {S : Type _} [CommRing S] (d : ℕ)

theorem mk_one_pow_eq_mk_choose_add :
    (@mk S 1) ^ (d + 1) = @mk S fun n => Nat.choose (d + n) d := by
  induction d with
  | zero => simp only [Nat.zero_eq, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one]; rfl
  | succ d hd =>
      rw [pow_add, pow_one, mul_comm, show Nat.succ d = d + 1 by rfl, ext_iff]; exact fun n => by
        rw [hd, coeff_mul]; simp only [coeff_mk, one_mul]; rw [Nat.succ_add, Nat.choose_succ_succ,
        ← Finset.sum_antidiagonal_choose_add]; simp only [Pi.one_apply, one_mul, Nat.cast_sum]

/--
The power series `mk fun n => Nat.choose (d + n) d`, whose multiplicative inverse is
`(1 - X) ^ (d + 1)`.
-/
noncomputable def invOneSubPow : S⟦X⟧ˣ where
  val := mk fun n => Nat.choose (d + n) d
  inv := (1 - X) ^ (d + 1)
  val_inv := by
    rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow,
      show (mk 1) * (1 - X : S⟦X⟧) = 1 by
      rw [mul_comm, ext_iff]; exact fun n => by
        by_cases hn : n = 0
        · subst hn; simp only [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one,
          constantCoeff_X, sub_zero, one_mul, coeff_one, ↓reduceIte]; rfl
        · simp only [one_mul, map_sub, coeff_mk, coeff_one, hn, ↓reduceIte];
          rw [show n = n - 1 + 1 by exact (Nat.succ_pred hn).symm, sub_mul];
          simp only [one_mul, map_sub, coeff_mk, Pi.one_apply, coeff_succ_X_mul, sub_self]]
    exact one_pow (d + 1)
  inv_val := by
    rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow,
      show (1 - X : S⟦X⟧) * (mk 1) = 1 by
      rw [ext_iff]; exact fun n => by
        by_cases hn : n = 0
        · subst hn; simp only [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one,
          constantCoeff_X, sub_zero, one_mul, coeff_one, ↓reduceIte]; rfl
        · rw [sub_mul]; simp only [one_mul, map_sub, coeff_mk, coeff_one, hn, ↓reduceIte];
          rw [show n = n - 1 + 1 by exact (Nat.succ_pred hn).symm, coeff_succ_X_mul];
          simp only [Pi.one_apply, coeff_mk, sub_self]]
    exact one_pow (d + 1)

theorem invOneSubPow_val_eq_mk_choose_add :
    (invOneSubPow d).val = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := rfl

theorem invOneSubPow_val_zero_eq_invUnitSub_one :
    (invOneSubPow 0).val = invUnitsSub (1 : Sˣ) := by
  rw [invOneSubPow, invUnitsSub]
  simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, one_pow, divp_one]

theorem invOneSubPow_eq_inv_one_sub_pow :
    invOneSubPow d = ⟨1 - X, invOfUnit (1 - X) 1, @mul_invOfUnit S _ (1 - X) 1 <| by
    simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
    rw [mul_comm]; exact @mul_invOfUnit S _ (1 - X) 1 <| by
      simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one]⟩⁻¹ ^ (d + 1) := by
  rw [inv_pow]; exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow d) <| by
  rw [← Units.val_eq_one, Units.val_mul, Units.val_pow_eq_pow_val];
  exact (invOneSubPow d).inv_val).symm

theorem invOneSubPow_inv_eq_one_sub_pow :
    (invOneSubPow d).inv = (1 - X : S⟦X⟧) ^ (d + 1) := rfl

theorem invOneSubPow_val_mul_one_sub_pow_eq_one :
    (invOneSubPow d).val * ((1 - X : S⟦X⟧) ^ (d + 1)) = 1 :=
  (invOneSubPow d).val_inv

theorem one_sub_pow_mul_invOneSubPow_val_eq_one :
    ((1 - X : S⟦X⟧) ^ (d + 1)) * (invOneSubPow d).val = 1 :=
  (invOneSubPow d).inv_val

theorem mk_choose_add_mul_one_sub_pow_eq_one :
    (mk fun n => Nat.choose (d + n) d : S⟦X⟧) * ((1 - X) ^ (d + 1)) = 1 :=
  (invOneSubPow d).val_inv

theorem one_sub_pow_mul_mk_choose_add_eq_one :
    ((1 - X) ^ (d + 1)) * (mk fun n => Nat.choose (d + n) d : S⟦X⟧) = 1 :=
  (invOneSubPow d).inv_val

end invOneSubPow

end Ring

section Field

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

/-- Power series for the exponential function at zero. -/
def exp : PowerSeries A :=
  mk fun n => algebraMap ℚ A (1 / n !)
#align power_series.exp PowerSeries.exp

/-- Power series for the sine function at zero. -/
def sin : PowerSeries A :=
  mk fun n => if Even n then 0 else algebraMap ℚ A ((-1) ^ (n / 2) / n !)
#align power_series.sin PowerSeries.sin

/-- Power series for the cosine function at zero. -/
def cos : PowerSeries A :=
  mk fun n => if Even n then algebraMap ℚ A ((-1) ^ (n / 2) / n !) else 0
#align power_series.cos PowerSeries.cos

variable {A A'} [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A'] (n : ℕ) (f : A →+* A')

@[simp]
theorem coeff_exp : coeff A n (exp A) = algebraMap ℚ A (1 / n !) :=
  coeff_mk _ _
#align power_series.coeff_exp PowerSeries.coeff_exp

@[simp]
theorem constantCoeff_exp : constantCoeff A (exp A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exp]
  simp
#align power_series.constant_coeff_exp PowerSeries.constantCoeff_exp

set_option linter.deprecated false in
@[simp]
theorem coeff_sin_bit0 : coeff A (bit0 n) (sin A) = 0 := by
  rw [sin, coeff_mk, if_pos (even_bit0 n)]
#align power_series.coeff_sin_bit0 PowerSeries.coeff_sin_bit0

set_option linter.deprecated false in
@[simp]
theorem coeff_sin_bit1 : coeff A (bit1 n) (sin A) = (-1) ^ n * coeff A (bit1 n) (exp A) := by
  rw [sin, coeff_mk, if_neg n.not_even_bit1, Nat.bit1_div_two, ← mul_one_div, map_mul, map_pow,
    map_neg, map_one, coeff_exp]
#align power_series.coeff_sin_bit1 PowerSeries.coeff_sin_bit1

set_option linter.deprecated false in
@[simp]
theorem coeff_cos_bit0 : coeff A (bit0 n) (cos A) = (-1) ^ n * coeff A (bit0 n) (exp A) := by
  rw [cos, coeff_mk, if_pos (even_bit0 n), Nat.bit0_div_two, ← mul_one_div, map_mul, map_pow,
    map_neg, map_one, coeff_exp]
#align power_series.coeff_cos_bit0 PowerSeries.coeff_cos_bit0

set_option linter.deprecated false in
@[simp]
theorem coeff_cos_bit1 : coeff A (bit1 n) (cos A) = 0 := by
  rw [cos, coeff_mk, if_neg n.not_even_bit1]
#align power_series.coeff_cos_bit1 PowerSeries.coeff_cos_bit1

@[simp]
theorem map_exp : map (f : A →+* A') (exp A) = exp A' := by
  ext
  simp
#align power_series.map_exp PowerSeries.map_exp

@[simp]
theorem map_sin : map f (sin A) = sin A' := by
  ext
  simp [sin, apply_ite f]
#align power_series.map_sin PowerSeries.map_sin

@[simp]
theorem map_cos : map f (cos A) = cos A' := by
  ext
  simp [cos, apply_ite f]
#align power_series.map_cos PowerSeries.map_cos

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
  refine' RingHom.congr_arg _ _
  rw [mul_one_div (↑(n.choose x) : ℚ), one_div_mul_one_div]
  symm
  rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial]
  norm_cast
  rw [cast_div_charZero]
  · apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]
#align power_series.exp_mul_exp_eq_exp_add PowerSeries.exp_mul_exp_eq_exp_add

/-- Shows that $e^{x} * e^{-x} = 1$ -/
theorem exp_mul_exp_neg_eq_one [Algebra ℚ A] : exp A * evalNegHom (exp A) = 1 := by
  convert exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp
#align power_series.exp_mul_exp_neg_eq_one PowerSeries.exp_mul_exp_neg_eq_one

/-- Shows that $(e^{X})^k = e^{kX}$. -/
theorem exp_pow_eq_rescale_exp [Algebra ℚ A] (k : ℕ) : exp A ^ k = rescale (k : A) (exp A) := by
  induction' k with k h
  · simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero, zero_eq,
      pow_zero (exp A), coe_comp]
  · simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
    id_apply, rescale_one] using pow_succ' (exp A) k
#align power_series.exp_pow_eq_rescale_exp PowerSeries.exp_pow_eq_rescale_exp

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
#align power_series.exp_pow_sum PowerSeries.exp_pow_sum

end PowerSeries
