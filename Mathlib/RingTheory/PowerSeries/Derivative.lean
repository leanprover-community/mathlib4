/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill, Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Formal derivatives of univariate power series

This file defines `PowerSeries.derivative`, the formal derivative of a univariate
power series, as a `Derivation R R⟦X⟧ R⟦X⟧`.

See also `MvPowerSeries.pderiv` for the multivariate setting.

## Main definitions

- `PowerSeries.derivative`: the formal derivative, as a derivation.

## Main results

- `PowerSeries.coeff_derivative`: coefficient formula
  `coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1)`.
- `PowerSeries.derivative_coe`: compatibility with `Polynomial.derivative`.
- `PowerSeries.trunc_derivative`: truncation commutes with differentiation.
- `PowerSeries.derivative.ext`: a power series is determined by its constant term and derivative.
- `PowerSeries.derivative_pow`: power rule.
- `PowerSeries.derivative_inv`, `PowerSeries.derivative_inv'`: derivative of an inverse.
- `PowerSeries.derivative_subst`: chain rule for power series substitution.
-/

@[expose] public section

namespace PowerSeries

open Polynomial Derivation Nat

variable {R : Type*}

section CommutativeSemiring

variable [CommSemiring R]

variable (R) in
/-- The formal derivative of a formal power series -/
noncomputable def derivative : Derivation R R⟦X⟧ R⟦X⟧ :=
  MvPowerSeries.pderiv R ()

/-- Abbreviation of `PowerSeries.derivative`, the formal derivative on `R⟦X⟧` -/
scoped notation "d⁄dX" => derivative

@[simp] theorem derivative_C {r : R} : d⁄dX R (C r) = 0 := MvPowerSeries.pderiv_C

theorem derivative_one : d⁄dX R 1 = 0 := MvPowerSeries.pderiv_one

theorem coeff_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (d⁄dX R f) = coeff (n + 1) f * (n + 1) := by
  simp [coeff, derivative, MvPowerSeries.coeff_pderiv]

theorem derivative_coe (f : R[X]) : d⁄dX R f = Polynomial.derivative f := by
  ext
  rw [coeff_derivative, coeff_coe, coeff_coe, Polynomial.coeff_derivative]

@[simp] theorem derivative_X : d⁄dX R (X : R⟦X⟧) = 1 :=
  MvPowerSeries.pderiv_X_self

-- We can't use `MvPowerSeries.trunc_pderiv` in the following proof,
-- since `PowerSeries.trunc` is not defined in terms of `MvPowerSeries.trunc`.
theorem trunc_derivative (f : R⟦X⟧) (n : ℕ) :
    trunc n (d⁄dX R f) = Polynomial.derivative (trunc (n + 1) f) := by
  ext d
  rw [coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative, Polynomial.coeff_derivative, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [Polynomial.coeff_derivative, coeff_trunc, if_neg this, zero_mul]

theorem trunc_derivative' (f : R⟦X⟧) (n : ℕ) :
    trunc (n - 1) (d⁄dX R f) = Polynomial.derivative (trunc n f) := by
  cases n <;> simp [trunc_derivative]

/-- The derivative of `g^n` equals `n * g^(n-1) * g'`. -/
theorem derivative_pow (g : R⟦X⟧) (n : ℕ) :
    d⁄dX R (g ^ n) = n * g ^ (n - 1) * d⁄dX R g :=
  MvPowerSeries.pderiv_pow g n

end CommutativeSemiring

/-- If `f` and `g` have the same constant term and derivative, then they are equal. -/
theorem derivative.ext [CommRing R] [IsAddTorsionFree R] {f g} (hD : d⁄dX R f = d⁄dX R g)
    (hc : constantCoeff f = constantCoeff g) : f = g :=
  MvPowerSeries.pderiv.ext (fun _ => hD) hc

@[simp]
theorem derivative_inv [CommRing R] (f : R⟦X⟧ˣ) :
    d⁄dX R ↑f⁻¹ = -(↑f⁻¹ : R⟦X⟧) ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv f

@[simp]
theorem derivative_invOf [CommRing R] (f : R⟦X⟧) [Invertible f] :
    d⁄dX R ⅟f = -⅟f ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv R⟦X⟧` for more general base rings `R`.
-/

@[simp] theorem derivative_inv' [Field R] (f : R⟦X⟧) : d⁄dX R f⁻¹ = -f⁻¹ ^ 2 * d⁄dX R f :=
  MvPowerSeries.pderiv_inv' f

/-- Chain rule for polynomials viewed as power series.  Use `derivative_subst` instead. -/
private theorem derivative_subst_coe [CommRing R] (p : Polynomial R) {g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R ((p : R⟦X⟧).subst g) = (d⁄dX R (p : R⟦X⟧)).subst g * d⁄dX R g := by
  simp [subst_coe hg, derivative_coe, Derivation.comp_aeval_eq (a := g) (derivative R) p,
    smul_eq_mul]

theorem derivative_subst [CommRing R] {f g : R⟦X⟧} (hg : HasSubst g) :
    d⁄dX R (f.subst g) = (d⁄dX R f).subst g * d⁄dX R g := by
  ext n
  obtain ⟨m, hm⟩ := (hg.eventually_coeff_pow_eq_zero (n + 1)).exists_forall_of_atTop
  have : coeff (n + 1) (f.subst g) = coeff (n + 1) ((↑(trunc (m + 1) f) : R⟦X⟧).subst g) := by
    rw [coeff_subst' hg, coeff_subst' hg]
    refine finsum_congr fun d ↦ ?_
    obtain hd | hd := lt_or_ge d m
    · rw [coeff_coe_trunc_of_lt (by lia)]
    · simp [coeff_trunc, hd, hm]
  rw [coeff_derivative, this, ← coeff_derivative, derivative_subst_coe _ hg, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
  congr 1
  simp only [coeff_subst' hg, coeff_derivative, coeff_coe, coeff_trunc]
  exact finsum_congr fun d ↦ by split_ifs <;> simp (disch := grind [Finset.mem_antidiagonal]) [hm]

section deprecated

variable [CommSemiring R]

/--
The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
derivation `derivative` on `R⟦X⟧`.
-/
@[deprecated derivative (since := "2026-06-26")]
noncomputable def derivativeFun (f : R⟦X⟧) := (derivative R).toFun f

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_add" (since := "2026-06-26")]
theorem derivativeFun_add (f g : R⟦X⟧) :
    derivativeFun (f + g) = derivativeFun f + derivativeFun g :=
  (derivative R).map_add f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.leibniz" (since := "2026-06-26")]
theorem derivativeFun_mul (f g : R⟦X⟧) :
    derivativeFun (f * g) = f • g.derivativeFun + g • f.derivativeFun :=
  (derivative R).leibniz f g

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_one_eq_zero" (since := "2026-06-26")]
theorem derivativeFun_one : derivativeFun (1 : R⟦X⟧) = 0 :=
  (derivative R).map_one_eq_zero

set_option linter.deprecated false in
@[deprecated "Use Derivation.map_smul" (since := "2026-06-26")]
theorem derivativeFun_smul (r : R) (f : R⟦X⟧) : derivativeFun (r • f) = r • derivativeFun f :=
  (derivative R).map_smul r f

@[deprecated (since := "2026-06-26")] alias derivativeFun_C := derivative_C

@[deprecated (since := "2026-06-26")] alias coeff_derivativeFun := coeff_derivative

@[deprecated (since := "2026-06-26")] alias derivativeFun_coe := derivative_coe

@[deprecated (since := "2026-06-26")] alias trunc_derivativeFun := trunc_derivative

end deprecated

end PowerSeries
