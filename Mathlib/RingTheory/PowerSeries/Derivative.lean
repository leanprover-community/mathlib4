/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Derivation.Basic

/-!
# Definitions

In this file we define an operation `derivative` (formal differentiation)
on the ring of formal power series in one variable (over an arbitrary commutative semiring).

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This will give us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
$\exp ( \log (1+X)) = 1+X$ by differentiating twice.

## Main Definition

- `PowerSeries.derivative R : Derivation R R⟦X⟧ R⟦X⟧` the formal derivative operation.
  This is abbreviated `d⁄dX R`.
-/

namespace PowerSeries

open Polynomial Derivation Nat

section CommutativeSemiring
variable {R} [CommSemiring R]

/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `derivative` on `R⟦X⟧`.
-/
noncomputable def derivativeFun (f : R⟦X⟧) : R⟦X⟧ := mk fun n ↦ coeff (n + 1) f * (n + 1)

theorem coeff_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    coeff n f.derivativeFun = coeff (n + 1) f * (n + 1) := by
  rw [derivativeFun, coeff_mk]

theorem derivativeFun_coe (f : R[X]) : (f : R⟦X⟧).derivativeFun = derivative f := by
  ext
  rw [coeff_derivativeFun, coeff_coe, coeff_coe, coeff_derivative]

theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g := by
  ext
  rw [coeff_derivativeFun, map_add, map_add, coeff_derivativeFun,
    coeff_derivativeFun, add_mul]

theorem derivativeFun_C (r : R) : derivativeFun (C r) = 0 := by
  ext n
  -- Note that `map_zero` didn't get picked up, apparently due to a missing `FunLike.coe`
  rw [coeff_derivativeFun, coeff_succ_C, zero_mul, (coeff n).map_zero]

theorem trunc_derivativeFun (f : R⟦X⟧) (n : ℕ) :
    trunc n f.derivativeFun = derivative (trunc (n + 1) f) := by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivativeFun, coeff_derivative, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivative, coeff_trunc, if_neg this, zero_mul]

--A special case of `derivativeFun_mul`, used in its proof.
private theorem derivativeFun_coe_mul_coe (f g : R[X]) : derivativeFun (f * g : R⟦X⟧) =
    f * derivative g + g * derivative f := by
  rw [← coe_mul, derivativeFun_coe, derivative_mul,
    add_comm, mul_comm _ g, ← coe_mul, ← coe_mul, Polynomial.coe_add]

/-- **Leibniz rule for formal power series**. -/
theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun := by
  ext n
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := Nat.lt_add_right _ h₁
  rw [coeff_derivativeFun, map_add, coeff_mul_eq_coeff_trunc_mul_trunc _ _ (lt_succ_self _),
    smul_eq_mul, smul_eq_mul, coeff_mul_eq_coeff_trunc_mul_trunc₂ g f.derivativeFun h₂ h₁,
    coeff_mul_eq_coeff_trunc_mul_trunc₂ f g.derivativeFun h₂ h₁, trunc_derivativeFun,
    trunc_derivativeFun, ← map_add, ← derivativeFun_coe_mul_coe, coeff_derivativeFun]

theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 := by
  rw [← map_one C, derivativeFun_C (1 : R)]

theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivativeFun_mul, derivativeFun_C, smul_zero, add_zero,
    smul_eq_mul]

variable (R)

/-- The formal derivative of a formal power series -/
noncomputable def derivative : Derivation R R⟦X⟧ R⟦X⟧ where
  toFun := derivativeFun
  map_add' := derivativeFun_add
  map_smul' := derivativeFun_smul
  map_one_eq_zero' := derivativeFun_one
  leibniz' := derivativeFun_mul
/-- Abbreviation of `PowerSeries.derivative`, the formal derivative on `R⟦X⟧` -/
scoped notation "d⁄dX" => derivative

variable {R}

@[simp] theorem derivative_C (r : R) : d⁄dX R (C r) = 0 := derivativeFun_C r

theorem coeff_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1) := coeff_derivativeFun f n

theorem derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f := derivativeFun_coe f

@[simp] theorem derivative_X : d⁄dX R (X : R⟦X⟧) = 1 := by
  ext
  rw [coeff_derivative, coeff_one, coeff_X, boole_mul]
  simp_rw [add_eq_right]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_derivative (f : R⟦X⟧) (n : ℕ) :
    trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f) :=
  trunc_derivativeFun ..

theorem trunc_derivative' (f : R⟦X⟧) (n : ℕ) :
    trunc (n - 1) (d⁄dX R f) = Polynomial.derivative (trunc n f) := by
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [succ_sub_one, trunc_derivative]

end CommutativeSemiring

/- In the next lemma, we use `smul_right_inj`, which requires not only `NoZeroSMulDivisors ℕ R`, but
also cancellation of addition in `R`. For this reason, the next lemma is stated in the case that `R`
is a `CommRing`. -/

/-- If `f` and `g` have the same constant term and derivative, then they are equal. -/
theorem derivative.ext {R} [CommRing R] [NoZeroSMulDivisors ℕ R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, hc]
  | succ n =>
    have equ : coeff n (d⁄dX R f) = coeff n (d⁄dX R g) := by rw [hD]
    rwa [coeff_derivative, coeff_derivative, ← cast_succ, mul_comm, ← nsmul_eq_mul,
      mul_comm, ← nsmul_eq_mul, smul_right_inj n.succ_ne_zero] at equ

@[simp] theorem derivative_inv {R} [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑f⁻¹ = -(↑f⁻¹ : R⟦X⟧) ^ 2 * d⁄dX R f := by
  apply Derivation.leibniz_of_mul_eq_one
  simp

@[simp] theorem derivative_invOf {R} [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R ⅟f = -⅟f ^ 2 * d⁄dX R f := by
  rw [Derivation.leibniz_invOf, smul_eq_mul]

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv R⟦X⟧` for more general base rings `R`.
-/
@[simp] theorem derivative_inv' {R} [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f := by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact PowerSeries.inv_mul_cancel (h := h)

end PowerSeries
