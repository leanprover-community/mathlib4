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

The Bessel function $J_a(x)$ has the representation
$$
J_a(x) = (x / 2)^a \frac{₀F₁(-; a + 1; -(x/2)^2)} {Γ(a + 1)}
$$
where $₀F₁$ is the hypergeometric function.
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

local notation "F₀₁(" a ")" => regularizedHGFun 0 {(a : ℂ)}

/-- Bessel function of the first kind $J_a(x)$. -/
@[pp_nodot, dlmf 10.2.E2]
noncomputable def besselJ (a x : ℂ) := (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2)

local notation "J" => besselJ

theorem besselJ_def : J = fun a x ↦ (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2) := rfl

/-- `J a` is even or odd when $a$ is even or odd, respectively. -/
theorem besselJ_int_neg (a : ℤ) (x : ℂ) : J a (-x) = (-1) ^ a * J a x := by
  simp [besselJ_def, ← mul_assoc, neg_div, ← mul_zpow]

theorem odd_besselJ {a : ℤ} (ha : Odd a) : Function.Odd (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

theorem even_besselJ {a : ℤ} (ha : Even a) : Function.Even (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

/-- `J a` is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ (J a) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselJ]

@[fun_prop]
theorem analyticOnNhd_besselJ (a : ℂ) : AnalyticOnNhd ℂ (J a) slitPlane :=
  fun _ hz ↦ analyticAt_besselJ a hz

/-- For integer `a`, `J a` and `J (-a)` are related by a sign. -/
@[dlmf 10.4.E1]
theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J (-a) x = (-1) ^ a * J a x := by
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

theorem besselJ_neg_comm (a : ℤ) (x : ℂ) : J (-a) x = J a (-x) := by
  rw [besselJ_neg_int, ← besselJ_int_neg]

/-- `J a` is analytic for integer `a`. -/
@[fun_prop]
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (J a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    have : AnalyticAt ℂ (fun x ↦ ((-1) ^ a)⁻¹ * J (↑(-a)) x) x := by fun_prop
    have ha' : (-1 : ℂ) ^ a ≠ 0 := by grind [zpow_ne_zero]
    simpa [besselJ_neg_int, ← mul_assoc, inv_mul_cancel₀ ha']
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have : AnalyticAt ℂ (fun x ↦ (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2)) x := by fun_prop
  simpa [besselJ_def]

@[fun_prop]
theorem analyticOnNhd_besselJ_int (a : ℤ) : AnalyticOnNhd ℂ (J a) .univ :=
  fun z _ ↦ analyticAt_besselJ_int a z

theorem besselJ_zero (a : ℂ) : J a 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselJ, h, regularizedHGFunCoeff]

@[dlmf 10.6.E1]
theorem two_mul_self_mul_besselJ (a : ℂ) (x : ℂ) :
    2 * a * J a x = x * J (a - 1) x + x * J (a + 1) x := by
  by_cases h : x = 0
  · simp [h, besselJ_zero]
  have h : x / 2 ≠ 0 := by simp_all
  unfold besselJ
  calc
    _ = 2 * (x / 2) ^ a * (a * F₀₁(a + 1) (-(x / 2) ^ 2)) := by
      ring
    _ = 2 * (x / 2) ^ a * F₀₁(a) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ a * (x / 2) ^ 2 * F₀₁(a + 2) (-(x / 2) ^ 2) := by
      rw [← sub_eq_iff_eq_add.mpr (regularizedHGFun_zero_singleton_eq_mul_add_mul a (-(x / 2) ^ 2))]
      ring_nf
    _ = 2 * ((x / 2) ^ (a - 1) * (x / 2) ^ (1 : ℂ)) * F₀₁(a) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ (a + 1) * (x / 2) * F₀₁(a + 2) (-(x / 2) ^ 2) := by
      rw [← cpow_add _ _ h, sub_add_cancel, cpow_add _ _ h, cpow_one]
      ring
    _ = _ := by
      rw [cpow_one]
      ring_nf

end Complex
