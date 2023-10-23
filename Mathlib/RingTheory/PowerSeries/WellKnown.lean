/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Comp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.BigOperators.NatAntidiagonal

#align_import ring_theory.power_series.well_known from "leanprover-community/mathlib"@"8199f6717c150a7fe91c4534175f4cf99725978f"

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

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

end Ring


/--
A power series `f` over a commutative ring `R` is a unit
if and only if its constant coefficient is a unit.
-/
@[simp] theorem isUnit_iff {R} [CommRing R] {f} : (IsUnit f) ↔ IsUnit (constantCoeff R f) := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := hf
    apply isUnit_of_mul_eq_one (b := constantCoeff R g.inv)
    rw [←hg, ←map_mul, Units.inv_eq_val_inv, Units.mul_inv, map_one]
  · intro hf
    obtain ⟨a : Rˣ,ha⟩ := hf
    have hf : f = (C R a - X) ∘ᶠ (C R a - f)
    · rw [sub_comp C_hasComp X_hasComp, C_comp, X_comp, sub_sub_cancel]
    have : f * (invUnitsSub a) ∘ᶠ (C R a - f) = 1
    · nth_rw 1 [hf]
      rw [←mul_comp, mul_comm, invUnitsSub_mul_sub, one_comp] <;>
      · apply hasComp_of_constantCoeff_eq_zero
        rw [map_sub, constantCoeff_C, ha, sub_self]
    apply isUnit_of_mul_eq_one (h := this)



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




namespace PowerSeries

open Nat hiding pow_zero pow_succ pow_succ'

variable {R} [Field R] [CharZero R]

/--
The formal power series `log(1 + X)`, i.e. `X - X^2/2 + X^3/3 - X^4/4 + ...`.
-/
def logOneAdd : R⟦X⟧ := mk fun n ↦ -(-1) ^ n / n


/--
The formal power series `1/(1 + X)`, i.e. `1 - X + X^2 - X^3 + X^4 - ...`.
-/
def alternatingGeometric : R⟦X⟧ := mk fun n ↦ (-1) ^ n


/--
The formal power series of the polylogarithm.

`polylog d = ∑ n^-d * X^n`
-/
def polylog (d : ℕ) : R⟦X⟧ := mk fun n ↦ (n : R)⁻¹ ^ d

local notation "exp" => exp _

theorem alternatingGeometric_eq : alternatingGeometric (R := R) = (1 + X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_add, mul_one]
  · ext n
    rw [map_add, alternatingGeometric]
    cases n with
    | zero =>
      rw [coeff_zero_mul_X, add_zero, coeff_mk, pow_zero, coeff_zero_eq_constantCoeff, map_one]
    | succ n =>
      rw [coeff_succ_mul_X, coeff_mk, coeff_mk, pow_succ, neg_one_mul, neg_add_self, coeff_one,
        if_neg n.succ_ne_zero]
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

theorem fDerivative_alternatingGeometric : d⁄dX R alternatingGeometric = -(1 + X)⁻¹ ^ 2 := by
  rw [alternatingGeometric_eq, fDerivative_inv', map_add, fDerivative_one, fDerivative_X, zero_add,
    mul_one]

@[simp] theorem fDerivative_exp : d⁄dX R exp = exp := by
  ext n
  simp only [coeff_exp, coeff_fDerivative, factorial_succ, cast_mul, cast_add, cast_one, mul_comm,
    ←div_div, one_div, map_div₀, map_inv₀, map_natCast, map_add, map_one, smul_eq_mul, mul_div]
  rw [mul_div_cancel]
  exact cast_add_one_ne_zero n

@[simp] theorem exp_neg {f : R⟦X⟧} (hf : constantCoeff R f = 0) :
    exp ∘ᶠ (-f) = (exp ∘ᶠ f)⁻¹ := by
  have : constantCoeff R (-f) = 0 := by rwa [map_neg, neg_eq_zero]
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · apply fDerivative.ext
    · rw [Derivation.leibniz, fDerivative_comp', fDerivative_comp', fDerivative_exp,
        fDerivative_one, map_neg, mul_neg, smul_neg, smul_eq_mul, smul_eq_mul,
        ←mul_assoc, mul_comm (exp ∘ᶠ (-f) : R⟦X⟧), mul_assoc, add_neg_self]
      exact this
      exact hf
    · rw [map_mul, constantCoeff_comp hf, constantCoeff_comp this,
        constantCoeff_exp, map_one, mul_one]
  · rw [constantCoeff_comp hf, constantCoeff_exp]
    exact one_ne_zero

@[simp] theorem exp_add (f g : R⟦X⟧) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
    exp ∘ᶠ (f + g) = exp ∘ᶠ f * exp ∘ᶠ g := by
  have eq : constantCoeff R (f + g) = 0 := by rw [map_add, hf, hg, zero_add]
  suffices : 1 = exp ∘ᶠ f * exp ∘ᶠ g * exp ∘ᶠ (-(f + g))
  · rwa [exp_neg, MvPowerSeries.eq_mul_inv_iff_mul_eq, one_mul] at this
    change constantCoeff R (exp ∘ᶠ (f + g)) ≠ 0
    rw [constantCoeff_comp eq, constantCoeff_exp]
    exact one_ne_zero
    rw [map_add, hf, hg, add_zero]
  apply fDerivative.ext
  · rw [fDerivative_mul, fDerivative_mul, fDerivative_comp', fDerivative_comp', fDerivative_comp',
      fDerivative_exp, fDerivative_one, map_neg, map_add]
    ring
    exact hf
    exact hg
    rwa [map_neg, neg_eq_zero]
  · rw [map_mul, map_mul, constantCoeff_comp hf, constantCoeff_comp hg, constantCoeff_comp,
      constantCoeff_exp, map_one, mul_one, mul_one]
    rw [map_neg, eq, neg_zero]

@[simp] theorem constantCoeff_logOneAdd : constantCoeff R logOneAdd = 0 := by
  rw [← coeff_zero_eq_constantCoeff, logOneAdd, coeff_mk, cast_zero, div_zero]

theorem hasComp_logOneAdd {f : R⟦X⟧} : f.hasComp logOneAdd := by
  apply hasComp_of_constantCoeff_eq_zero constantCoeff_logOneAdd

@[simp] theorem fDerivative_logOneAdd : d⁄dX R logOneAdd = (1 + X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  ext n
  rw [mul_add, mul_one, map_add, coeff_fDerivative, logOneAdd, coeff_mk, cast_add,
    cast_one, div_mul_cancel]
  cases n with
  | zero =>
    rw [coeff_zero_mul_X, coeff_zero_one, pow_succ, pow_zero, mul_one, add_zero, neg_neg]
  | succ n =>
    have : n + 1 ≠ 0 := succ_ne_zero n
    rw [coeff_succ_mul_X, coeff_fDerivative, coeff_mk, coeff_one, cast_add, cast_one,
      div_mul_cancel, pow_succ, neg_one_mul, succ_eq_add_one, neg_add_self, if_neg this]
    rwa [←cast_one, ←cast_add, cast_ne_zero]
  · rw [←cast_one, ←cast_add, cast_ne_zero]
    exact succ_ne_zero n
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

theorem const_exp_sub_one : constantCoeff R (exp - 1) = 0 := by
  rw [map_sub, constantCoeff_exp, constantCoeff_one, sub_self]

theorem hasComp_exp_sub_one {f : R⟦X⟧} : f.hasComp (exp - 1) := by
  apply hasComp_of_constantCoeff_eq_zero const_exp_sub_one

theorem fDerivative_log_comp_exp : d⁄dX R (logOneAdd ∘ᶠ (exp - 1)) = 1 := by
  rw [fDerivative_comp' const_exp_sub_one, fDerivative_logOneAdd, map_sub, fDerivative_one,
    sub_zero, fDerivative_exp]
  have : (1 + X : R⟦X⟧) ∘ᶠ (exp - 1) = exp
  · rw [add_comp hasComp_exp_sub_one hasComp_exp_sub_one,
      X_comp, one_comp, add_sub_cancel'_right]
  · nth_rw 2 [← this]
    rw [← mul_comp hasComp_exp_sub_one hasComp_exp_sub_one,
      PowerSeries.inv_mul_cancel, one_comp]
    rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

@[simp] theorem logOneAdd_comp_exp_sub_one : (logOneAdd ∘ᶠ (exp - 1) : R⟦X⟧) = X := by
  apply fDerivative.ext
  · rw [fDerivative_log_comp_exp, fDerivative_X]
  · rw [constantCoeff_comp const_exp_sub_one, constantCoeff_X, constantCoeff_logOneAdd]

theorem logOneAdd_comp_mul_sub_one (f g : R⟦X⟧) (hf : constantCoeff R f = 0)
    (hg : constantCoeff R g = 0) :
    (logOneAdd ∘ᶠ ((1 + f) * (1 + g) - 1)) = logOneAdd ∘ᶠ f + logOneAdd ∘ᶠ g := by
  have eq : constantCoeff R ((1 + f) * (1 + g) - 1) = 0 := by
    rw [map_sub, map_mul, map_add, map_add, hf, hg, map_one, add_zero, mul_one, sub_self]
  have : constantCoeff R (1 + X) ≠ 0
  · rw [map_add, map_one, constantCoeff_X, add_zero]; exact one_ne_zero
  apply fDerivative.ext
  · rw [fDerivative_comp' eq, map_sub, fDerivative_mul, map_add, map_add, map_add, fDerivative_one,
      fDerivative_comp' hf, fDerivative_comp' hg, zero_add, sub_zero, zero_add, mul_add,
      fDerivative_logOneAdd, add_comm]
    congr 1
    · rw [inv_comp' this eq, add_comp one_hasComp X_hasComp, one_comp, X_comp,
        add_comm, sub_add_cancel, inv_comp' this hf, add_comp one_hasComp X_hasComp,
        one_comp, X_comp, ←mul_assoc, PowerSeries.mul_inv_rev,
        mul_comm (1 + g)⁻¹, mul_assoc (1 + f)⁻¹, PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hg, add_zero]; exact one_ne_zero
    · rw [inv_comp' this eq, add_comp one_hasComp X_hasComp, one_comp, X_comp,
        add_comm, sub_add_cancel, inv_comp' this hg, add_comp one_hasComp X_hasComp,
        one_comp, X_comp, ← mul_assoc, PowerSeries.mul_inv_rev, mul_assoc (1 + g)⁻¹,
        PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hf, add_zero]; exact one_ne_zero
  · rw [constantCoeff_comp eq, map_add, constantCoeff_comp hf, constantCoeff_comp hg,
      constantCoeff_logOneAdd, add_zero]

@[simp] theorem exp_comp_logOneAdd : exp ∘ᶠ logOneAdd = (1 + X : R⟦X⟧) := by
  apply fDerivative.ext
  · rw [fDerivative_comp' constantCoeff_logOneAdd, map_add, fDerivative_one, zero_add,
      fDerivative_exp]
    apply fDerivative.ext
    · rw [fDerivative_mul, fDerivative_comp' constantCoeff_logOneAdd, fDerivative_exp,
        fDerivative_X, fDerivative_one, fDerivative_logOneAdd, fDerivative_inv', map_add,
        fDerivative_one, fDerivative_X, zero_add, mul_one, pow_two, mul_neg, ←mul_assoc,
        mul_comm, neg_add_self]
    · rw [fDerivative_X, map_one, fDerivative_logOneAdd, map_mul,
        constantCoeff_comp constantCoeff_logOneAdd, constantCoeff_inv, map_add, map_one,
        constantCoeff_X, add_zero, inv_one, mul_one, constantCoeff_exp]
  · rw [constantCoeff_comp constantCoeff_logOneAdd, constantCoeff_exp, map_add, constantCoeff_one,
      constantCoeff_X, add_zero]

theorem constantCoeff_polylog_succ (n : ℕ) : constantCoeff R (polylog n.succ) = 0 := by
  rw [polylog, ←coeff_zero_eq_constantCoeff, coeff_mk, pow_succ,
    cast_zero, inv_zero, zero_mul]

theorem fDerivative_polylog_one : d⁄dX R (polylog 1) = (1 - X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_sub, mul_one]
  · ext m
    cases m with
    | zero =>
      rw [map_sub, coeff_fDerivative, coeff_zero_mul_X, coeff_zero_eq_constantCoeff,
        sub_zero, cast_zero, zero_add, mul_one, map_one, polylog, coeff_mk,
        cast_one, pow_one, inv_one]
    | succ n =>
      rw [map_sub, coeff_succ_mul_X, coeff_one, polylog, coeff_fDerivative, coeff_fDerivative,
        coeff_mk, coeff_mk, pow_one, pow_one, cast_add, cast_add, cast_one, if_neg n.succ_ne_zero,
        inv_mul_cancel, inv_mul_cancel, sub_self] <;> apply cast_add_one_ne_zero
  · rw [map_sub, map_one, constantCoeff_X, sub_zero]
    exact one_ne_zero



theorem X_mul_X_polylog_succ (d : ℕ) : X * d⁄dX R (polylog (d + 2)) = polylog (d + 1) := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_polylog_succ]
  | succ n =>
    rw [coeff_succ_X_mul, polylog, polylog, coeff_mk, coeff_fDerivative, coeff_mk, ←cast_succ,
      succ_eq_add_one, pow_succ', mul_assoc, inv_mul_cancel, mul_one]
    rw [cast_ne_zero]
    exact n.succ_ne_zero

end PowerSeries
