/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
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

## TODO

* Bessel function of the second kind
* Differential equations
* Generating functions
* Bessel's integrals

-/

@[expose] public noncomputable section

open Nat FormalMultilinearSeries

namespace Complex

local notation "F₀₁(" a ")" => regularizedHGFun 0 {(a : ℂ) + 1}

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
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ (J(a)) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselJ]

/-- For integer `a`, `J(a)` and `J(-a)` are related by a sign. -/
theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J(-a) x = (-1) ^ a * J(a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    simp only [Int.cast_neg, neg_neg, zpow_neg] at this
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
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (J(a)) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    have : AnalyticAt ℂ (fun x ↦ ((-1) ^ a)⁻¹ * J(↑(-a)) x) x := by fun_prop
    have ha' : (-1 : ℂ) ^ a ≠ 0 := by grind [zpow_ne_zero]
    simpa [besselJ_neg_int, ← mul_assoc, inv_mul_cancel₀ ha']
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have : AnalyticAt ℂ (fun x ↦ (x / 2) ^ a * F₀₁(a) (- (x / 2) ^ 2)) x := by fun_prop
  simpa [besselJ_def]

theorem besselJ_zero (a : ℂ) : J(a) 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselJ, h, regularizedHGFunCoeff]

theorem self_mul_besselJ (a : ℂ) (x : ℂ) :
    2 * a * J(a) x = x * J(a - 1) x + x * J(a + 1) x := by
  by_cases h : x = 0
  · simp [h, besselJ_zero]
  have h : x / 2 ≠ 0 := by simp_all
  unfold besselJ
  calc
    _ = 2 * (x / 2) ^ a * (a * F₀₁(a) (-(x / 2) ^ 2)) := by
      ring
    _ = 2 * (x / 2) ^ a * F₀₁(a - 1) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ a * (x / 2) ^ 2 * F₀₁(a + 1) (-(x / 2) ^ 2) := by
      rw [← sub_eq_iff_eq_add.mpr (mul_regularizedHGFun_zero_singleton a (-(x / 2) ^ 2))]
      ring_nf
    _ = 2 * ((x / 2) ^ (a - 1) * (x / 2) ^ (1 : ℂ)) * F₀₁(a - 1) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ (a + 1) * (x / 2) * F₀₁(a + 1) (-(x / 2) ^ 2) := by
      rw [← cpow_add _ _ h, sub_add_cancel, cpow_add _ _ h, cpow_one]
      ring
    _ = _ := by
      rw [cpow_one]
      ring

theorem mul_deriv_besselJ_eq_besselJ_add_one (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x * deriv J(a) x = a * J(a) x - x * J(a + 1) x := by
  have hx2 : x / 2 ∈ slitPlane := by simpa [slitPlane] using h
  have hx0 : x / 2 ≠ 0 := by
    intro h
    simp_all
  unfold besselJ
  calc
    _ = x * (deriv (fun x ↦ (x / 2) ^ a) x * F₀₁(a) (-(x / 2) ^ 2) +
        (x / 2) ^ a * deriv ((fun x ↦ F₀₁(a) x) ∘ fun x ↦ -(x / 2) ^ 2) x) := by
      rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
      rfl
    _ = 2 * (x / 2) * deriv (fun x ↦ (x / 2) ^ a) x * F₀₁(a) (-(x / 2) ^ 2) + x *
        (x / 2) ^ a * (F₀₁(a + 1) (-(x / 2) ^ 2) * (-x / 2)) := by
      rw [deriv_comp _ (by fun_prop) (by fun_prop), deriv_regularizedHGFun (by simp)]
      simp
      ring
    _ = (a * (x / 2) ^ a) * F₀₁(a) (-(x / 2) ^ 2) + x *
        (x / 2) ^ a * (F₀₁(a + 1) (-(x / 2) ^ 2) * (-x / 2)) := by
      congrm ?_ * _ + _
      rw [_root_.deriv_cpow_const (by fun_prop) (by exact hx2)]
      trans 2 * a * ((x / 2) ^ (a - 1) * (x / 2) ^ (1 : ℂ) * deriv (fun x ↦ x / 2) x)
      · norm_cast
        ring
      rw [← cpow_add _ _ hx0]
      simp
      ring
    _ = _ := by
      rw [cpow_add _ _ hx0, cpow_one]
      ring

theorem mul_deriv_besselJ_eq_besselJ_sub_one (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x * deriv J(a) x = x * J(a - 1) x - a * J(a) x := by
  linear_combination self_mul_besselJ a x + mul_deriv_besselJ_eq_besselJ_add_one a h

theorem two_mul_deriv_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    2 * deriv J(a) x = J(a - 1) x - J(a + 1) x := by
  have hx0 : x ≠ 0 := by
    intro h
    simp_all
  rw [← mul_left_inj' hx0]
  linear_combination mul_deriv_besselJ_eq_besselJ_sub_one a h +
    mul_deriv_besselJ_eq_besselJ_add_one a h

theorem besselJ_neg_one (x : ℂ) : J(-1) x = -J(1) x := by
  simpa using besselJ_neg_int 1 x

open Topology

theorem two_mul_deriv_besselJ_int (a : ℤ) (x : ℂ) :
    2 * deriv J(a) x = J(a - 1) x - J(a + 1) x := by
  wlog! hx0 : x ≠ 0
  · suffices (fun _ ↦ 2) * deriv J(a) =ᶠ[𝓝 0] J(↑(a - 1)) - J(↑(a + 1)) by
      simpa [hx0] using this.eq_of_nhds
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (AnalyticAt.continuousAt (𝕜 := ℂ) (by fun_prop))
      (AnalyticAt.continuousAt (𝕜 := ℂ) (by fun_prop))]
    refine eventuallyEq_nhdsWithin_of_eqOn fun x hx ↦ ?_
    simpa using this a x (by simpa using hx)
  by_cases hx : x ∈ slitPlane
  · exact two_mul_deriv_besselJ a hx
  have hx' : -x ∈ slitPlane := by
    contrapose! hx0
    rw [Complex.ext_iff]
    simp_all [slitPlane]
    grind
  convert congr(- $(two_mul_deriv_besselJ (-a) hx'))
  · trans 2 * (deriv ((fun x ↦ J(a) (-x)) ∘ (-·)) x)
    · simp [Function.comp_def]
    simp_rw [← besselJ_neg_comm]
    norm_cast
    rw [deriv_comp _ (by fun_prop) (by fun_prop)]
    simp
  · norm_cast
    simp_rw [← besselJ_neg_comm]
    simp
    ring_nf

theorem mul_deriv_besselJ_eq_besselJ_add_one_int (a : ℤ) (x : ℂ) :
    x * deriv J(a) x = a * J(a) x - x * J(a + 1) x := by
  linear_combination x * two_mul_deriv_besselJ_int a x / 2 - self_mul_besselJ a x / 2

theorem mul_deriv_besselJ_eq_besselJ_sub_one_int (a : ℤ) (x : ℂ) :
    x * deriv J(a) x = x * J(a - 1) x - a * J(a) x := by
  linear_combination self_mul_besselJ a x + mul_deriv_besselJ_eq_besselJ_add_one_int a x

end Complex
