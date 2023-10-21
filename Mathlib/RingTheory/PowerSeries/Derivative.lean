/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Definitions

In this file we define an operation `fDerivative` (formal differentiation)
on the ring of formal power series in one variable (over an arbitrary commutative semiring).

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This will give us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
$\exp ( \log (1+X)) = 1+X$ by differentiating twice.

## Main Definition

- `PowerSeries.fDerivative R : Derivation R R⟦X⟧ R⟦X⟧` the formal derivative operation.
  This is abbreviated `d⁄dX R`.
-/

namespace PowerSeries

open Polynomial Derivation Nat

section CommutativeSemiring
variable {R} [CommSemiring R]

/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `fDerivative` on `R⟦X⟧`.
-/
noncomputable def fDerivativeFun (f : R⟦X⟧) : R⟦X⟧ := mk λ n ↦ coeff R (n + 1) f * (n + 1)

theorem coeff_fDerivativeFun (f : R⟦X⟧) (n : ℕ) :
    coeff R n f.fDerivativeFun = coeff R (n + 1) f * (n + 1) := by
  rw [fDerivativeFun, coeff_mk]

theorem fDerivativeFun_coe (f : R[X]) : (f : R⟦X⟧).fDerivativeFun = derivative f := by
  ext
  rw [coeff_fDerivativeFun, coeff_coe, coeff_coe, coeff_derivative]

theorem fDerivativeFun_add (f g : R⟦X⟧) :
    fDerivativeFun (f + g) = fDerivativeFun f + fDerivativeFun g := by
  ext
  rw [coeff_fDerivativeFun, map_add, map_add, coeff_fDerivativeFun,
    coeff_fDerivativeFun, add_mul]

theorem fDerivativeFun_C (r : R) : fDerivativeFun (C R r) = 0 := by
  ext n
  rw [coeff_fDerivativeFun, coeff_C]
  split_ifs with h
  · cases succ_ne_zero n h
  · rw [zero_mul, map_zero]

theorem trunc_fDerivativeFun (f : R⟦X⟧) (n : ℕ) :
    (trunc n f.fDerivativeFun : R⟦X⟧) = fDerivativeFun ↑(trunc (n + 1) f) := by
  ext d
  rw [coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_fDerivativeFun, coeff_fDerivativeFun, coeff_coe, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_fDerivativeFun, coeff_coe, coeff_trunc, if_neg this, zero_mul]

--A special case of `fDerivativeFun_mul`, used in its proof.
private theorem fDerivativeFun_coe_mul_coe (f g : R[X]) : fDerivativeFun (f * g : R⟦X⟧) =
    f * fDerivativeFun (g : R⟦X⟧) + g * fDerivativeFun (f : R⟦X⟧) := by
  rw [←coe_mul, fDerivativeFun_coe, derivative_mul, fDerivativeFun_coe, fDerivativeFun_coe,
    add_comm, mul_comm _ g, ←coe_mul, ←coe_mul, Polynomial.coe_add]

/-- Leibniz rule for formal power series.-/
theorem fDerivativeFun_mul (f g : R⟦X⟧) :
    fDerivativeFun (f * g) = f • g.fDerivativeFun + g • f.fDerivativeFun := by
  ext n
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := Nat.lt_add_right _ _ _ h₁
  rw [coeff_fDerivativeFun, map_add, coeff_mul_eq_coeff_trunc_mul_trunc _ _ (lt_succ_self _),
    smul_eq_mul, smul_eq_mul, coeff_mul_eq_coeff_trunc_mul_trunc₂ g f.fDerivativeFun h₂ h₁,
    coeff_mul_eq_coeff_trunc_mul_trunc₂ f g.fDerivativeFun h₂ h₁, trunc_fDerivativeFun,
    trunc_fDerivativeFun, ←map_add, ←fDerivativeFun_coe_mul_coe, coeff_fDerivativeFun]

theorem fDerivativeFun_one : fDerivativeFun (1 : R⟦X⟧) = 0 := by
  rw [←map_one (C R), fDerivativeFun_C (1 : R)]

theorem fDerivativeFun_smul (r : R) (f : R⟦X⟧) : fDerivativeFun (r • f) = r • fDerivativeFun f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, fDerivativeFun_mul, fDerivativeFun_C, smul_zero, add_zero,
    smul_eq_mul]

variable (R)
/--The formal derivative of a formal power series.-/
noncomputable def fDerivative : Derivation R R⟦X⟧ R⟦X⟧
where
  toFun             := fDerivativeFun
  map_add'          := fDerivativeFun_add
  map_smul'         := fDerivativeFun_smul
  map_one_eq_zero'  := fDerivativeFun_one
  leibniz'          := fDerivativeFun_mul
scoped notation "d⁄dX" => fDerivative

variable {R}

@[simp] theorem fDerivative_C (r : R) : d⁄dX R (C R r) = 0 := fDerivativeFun_C r

@[simp] theorem coeff_fDerivative (f : R⟦X⟧) (n : ℕ) : coeff R n (d⁄dX R f) = coeff R (n + 1) f * (n + 1) :=
  coeff_fDerivativeFun f n

theorem fDerivative_coe (f : R[X]) : d⁄dX R f = derivative f := fDerivativeFun_coe f

@[simp] theorem fDerivative_X : d⁄dX R (X : R⟦X⟧) = 1 := by
  ext
  rw [coeff_fDerivative, coeff_one, coeff_X, boole_mul]
  simp_rw [add_left_eq_self]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_fDerivative (f : R⟦X⟧) (n : ℕ) : trunc n (d⁄dX R f) = derivative (trunc (n + 1) f) := by
  apply Polynomial.coe_inj.mp
  rw [←fDerivative_coe]
  apply trunc_fDerivativeFun

theorem trunc_D' (f : R⟦X⟧) (n : ℕ) : trunc (n-1) (d⁄dX R f) = derivative (trunc n f) := by
  cases n with
  | zero =>
    simp only [zero_eq, ge_iff_le, tsub_eq_zero_of_le]
    rfl
  | succ n =>
    rw [succ_sub_one, trunc_fDerivative]

end CommutativeSemiring

/-In the next lemma, we use `smul_right_inj`, which requires not only `no_smul_divisors ℕ R`, but
also cancellation of addition in `R`. For this reason, the next lemma is stated in the case that `R`
is a `CommRing`.-/

/-- If `f` and `g` have the same constant term and derivative, then they are equal.-/
theorem fDerivative.ext {R} [CommRing R] [NoZeroSMulDivisors ℕ R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff R f = constantCoeff R g) : f = g := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, hc]
  | succ n =>
    have equ : coeff R n (d⁄dX (R := R) f) = coeff R n (d⁄dX (R := R) g) := by rw [hD]
    rwa [coeff_fDerivative, coeff_fDerivative, ←cast_succ, mul_comm, ←nsmul_eq_mul,
      mul_comm, ←nsmul_eq_mul, smul_right_inj] at equ
    exact n.succ_ne_zero

@[simp] theorem dDerivative_inv {R} [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑(f⁻¹) = -((f⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) ^ 2 * d⁄dX R f := by
  apply Derivation.leibniz_of_mul_eq_one
  simp

@[simp] theorem fDerivative_invOf {R} [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R (⅟ f) = - (⅟ f) ^ 2 * d⁄dX R f := by
  rw [Derivation.leibniz_invOf, smul_eq_mul]

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv R⟦X⟧` for more general base rings `R`.
-/
@[simp] theorem fDerivative_inv' {R} [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f := by
  by_cases constantCoeff R f = 0
  · suffices : f⁻¹ = 0
    rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact PowerSeries.inv_mul_cancel (h := h)

end PowerSeries
