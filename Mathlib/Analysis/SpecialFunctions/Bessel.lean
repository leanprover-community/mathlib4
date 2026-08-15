/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Evan Bailey
-/

module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!

# Bessel function

We introduce Bessel functions in this file. Bessel functions commonly take two complex parameters
`a` and `x`. They are analytic for `x ∈ Complex.slitPlane`. We also provide scoped notation in
the namespace `Complex` for these functions.

## `Complex.besselJ a x`: Bessel function of the first kind $J_a(x)$

Notation: `J(a) x`

An equation for $J_a(x)$ is
$$
J_a(x) = (x / 2)^a \frac{₀F₁(-; a + 1; -(x/2)^2)} {Γ(a + 1)}
$$
Based on this, we define `Complex.besselJ a x` using `Complex.regularizedHGFun` for the fraction
part which removes the singularity for negative integer $a$.

This function is analytic for all `x` when `a` is an integer. (see `Complex.analyticAt_besselJ_int`)

$J_a(0) = 0$ for all complex $a \ne 0$. For $a = 0$, we have $J_0(0) = 1$.
(See `Complex.besselJ_zero`)

## `Complex.besselI a x`: Modified Bessel function of the first kind $I_a(x)$

Notation: `I(a) x`

An equation for $I_a(x)$ is
$$
I_a(x) = (x / 2)^a \frac{₀F₁(-; a + 1; -(x/2)^2)} {Γ(a + 1)}
$$
`Complex.besselI a x` is defined analogously to `Complex.besselJ a x`.

Like `Complex.besselJ`, this function is analytic for all `x` when `a` is an integer.
(see `Complex.analyticAt_besselI_int`)

$I_a(0) = 0$ for all complex $a \ne 0$. For $a = 0$, we have $I_0(0) = 1$.
(See `Complex.besselI_zero`)

## TODO

* Bessel function of the second kind
* Differential equations
* Generating functions
* Bessel's integrals

-/

@[expose] public noncomputable section

open Nat FormalMultilinearSeries Real

/-! ## Bessel function of the first kind -/

namespace Complex

local notation "F₀₁(" a ")" => regularizedHGFun 0 {(a : ℂ) + 1}

section BesselJ

/-- Bessel function of the first kind $J_a(x)$. This has the notation `J(a) x` in the namespace
`Complex`. -/
noncomputable def besselJ (a x : ℂ) := (x / 2) ^ a * F₀₁(a) (- (x / 2) ^ 2)

@[inherit_doc besselJ] scoped notation3 "J(" a ")" => besselJ (a : ℂ)

theorem besselJ_def : besselJ = fun a x ↦ (x / 2) ^ a * F₀₁(a) (- (x / 2) ^ 2) := rfl

/-- `J(a)` is even or odd when $a$ is even or odd, respectively. -/
theorem besselJ_int_neg (a : ℤ) (x : ℂ) : J(a) (-x) = (-1) ^ a * J(a) x := by
  simp [besselJ_def, ← mul_assoc, neg_div, ← mul_zpow]

theorem odd_besselJ {a : ℤ} (ha : Odd a) : Function.Odd J(a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

theorem even_besselJ {a : ℤ} (ha : Even a) : Function.Even J(a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

/-- `J(a)` is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ J(a) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselJ]

@[fun_prop]
theorem analyticOnNhd_besselJ (a : ℂ) : AnalyticOnNhd ℂ J(a) slitPlane :=
  fun _ hz ↦ analyticAt_besselJ a hz

/-- For integer `a`, `J(a)` and `J(-a)` are related by a sign. -/
@[simp]
theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J(-a) x = (-1) ^ a * J(a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    rw [Int.cast_neg, neg_neg, zpow_neg] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  push_cast
  have h : (x / 2) ^ (a : ℂ) = (x / 2) ^ (-a : ℂ) * ((x / 2) ^ 2) ^ a := by
    by_cases hx : x = 0
    · by_cases ha : a = 0 <;> simp [hx, ha]
    rw [← pow_mul, ← cpow_natCast, ← cpow_add _ _ (by simpa using hx)]
    grind
  unfold besselJ
  rw [regularizedHGFun_zero_singleton_neg_nat_add_one, neg_pow, h, zpow_natCast]
  ring

theorem besselJ_neg_comm (a : ℤ) (x : ℂ) : J(-a) x = J(a) (-x) := by
  rw [besselJ_neg_int, ← besselJ_int_neg]

/-- `J(-a)` is analytic for integer `a`. -/
@[fun_prop]
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ J(a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    have : AnalyticAt ℂ (fun x ↦ ((-1) ^ a)⁻¹ * J(↑(-a)) x) x := by fun_prop
    have ha' : (-1 : ℂ) ^ a ≠ 0 := by grind [zpow_ne_zero]
    simpa [besselJ_neg_int, ← mul_assoc, inv_mul_cancel₀ ha']
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have : AnalyticAt ℂ (fun x ↦ (x / 2) ^ a * F₀₁(a) (- (x / 2) ^ 2)) x := by fun_prop
  simpa [besselJ_def]

@[fun_prop]
theorem analyticOnNhd_besselJ_int (a : ℤ) : AnalyticOnNhd ℂ J(a) .univ :=
  fun z _ ↦ analyticAt_besselJ_int a z

theorem besselJ_zero (a : ℂ) : J(a) 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselJ, h, regularizedHGFunCoeff]

end BesselJ

section BesselI

/-- Modified Bessel function of the first kind $I_a(x)$. This has the notation `I(a) x` in the
namespace `Complex`. -/
noncomputable def besselI (a x : ℂ) := (x / 2) ^ a * F₀₁(a) ((x / 2) ^ 2)

@[inherit_doc besselJ] scoped notation3 "I(" a ")" => besselI (a : ℂ)

theorem besselI_def : besselI = fun a x ↦ (x / 2) ^ a * F₀₁(a) ((x / 2) ^ 2) := rfl

/-- $I_a(x)$ is even or odd when $a$ is even or odd, respectively. -/
theorem besselI_int_neg (a : ℤ) (x : ℂ) : I(a) (-x) = (-1) ^ a * I(a) x := by
  simp [besselI_def, ← mul_assoc, neg_div, ← mul_zpow]

theorem odd_besselI {a : ℤ} (ha : Odd a) : Function.Odd I(a) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

theorem even_besselI {a : ℤ} (ha : Even a) : Function.Even I(a) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

/-- $I_a(x)$ is equal to $e^{-\frac{a\pi i}2} J_a(e^{\frac{\pi i}2} x) -/
theorem besselI_int_eq_neg_I_pow_mul_besselJ_I_mul (a : ℤ) (x : ℂ) :
    I(a) x = (-I) ^ a * J(a) (I * x) := by
  simp only [besselI_def, besselJ_def, ← zpow_natCast, ← mul_div, mul_zpow, ← neg_mul, cpow_intCast]
  simp only [← mul_assoc, zpow_natCast, I_sq, ← mul_zpow, neg_mul, I_mul_I, neg_neg, one_mul]

/-- $I_a(x)$ is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselI (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ I(a) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselI]

@[fun_prop]
theorem analyticOnNhd_besselI (a : ℂ) : AnalyticOnNhd ℂ I(a) slitPlane :=
  fun _ hz ↦ analyticAt_besselI a hz

/-- For integer $a$, $I_a(x)$ and $I_{-a}(x)$ are equal. -/
@[simp]
theorem besselI_neg_int (a : ℤ) (x : ℂ) : I(-a) x = I(a) x := by
  rw [← Int.cast_neg, besselI_int_eq_neg_I_pow_mul_besselJ_I_mul, Int.cast_neg, besselJ_neg_int,
    ← mul_assoc, ← I_sq, ← neg_sq, ← zpow_natCast, ← zpow_mul, ← zpow_add' (by simp),
    besselI_int_eq_neg_I_pow_mul_besselJ_I_mul]
  ring_nf

/-- $I_a(x)$ is analytic for integer $a$. -/
@[fun_prop]
theorem analyticAt_besselI_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ I(a) x := by
  rw [funext (besselI_int_eq_neg_I_pow_mul_besselJ_I_mul a)]
  fun_prop

@[fun_prop]
theorem analyticOnNhd_besselI_int (a : ℤ) : AnalyticOnNhd ℂ I(a) .univ :=
  fun z _ ↦ analyticAt_besselI_int a z

theorem besselI_zero (a : ℂ) : I(a) 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselI, h, regularizedHGFunCoeff]

end BesselI

end Complex
