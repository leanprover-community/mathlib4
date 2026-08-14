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

We introduce Bessel functions in this file.

## Main declarations

* `Complex.besselJ a x`: Bessel function of the first kind $J_a(x)$.

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
local notation "S₀₁(" a ")" => regularizedHGFunSeries 0 {(a : ℂ) + 1}
local notation "C₀₁(" a ")" => regularizedHGFunCoeff 0 {(a : ℂ) + 1}

/-- Bessel function of the first kind $J_a(x)$ for complex parameter $a$ and $x$, defined as
$$
J_a(x) = \frac{(x / 2)^a}{\Gamma(a + 1)} {}_0 F_1\left( -; a + 1; -\left(\frac{x}{2}\right)^2\right)
$$
with a branch cut on the negative real axis (See `Complex.analyticAt_besselJ`). We use
`Complex.regularizedHGFun` to include both $\Gamma(a + 1)$ and ${}_0 F_1$ and eliminate the
singularity for negative integer $a$.

For integer $a$, the branch cut vanishes and $J_a(x)$ is analytic on the entire complex plane
(See `Complex.analyticAt_besselJ_int`).

$J_a(0) = 0$ for all complex $a \ne 0$, which can be regarded as the junk value assigned
to non-integer $a$ (For integer $a$ this is well-defined and forced by analyticity). For $a = 0$,
we have $J_0(0) = 1$. (See `Complex.besselJ_zero`).
-/
noncomputable def besselJ (a x : ℂ) := (x / 2) ^ a * F₀₁(a) (- (x / 2) ^ 2)

local notation "J" => besselJ

/-- $J_a(x)$ is even or odd when $a$ is even or odd, respectively. -/
theorem besselJ_int_neg (a : ℤ) (x : ℂ) :
    J a (-x) = (-1) ^ a * J a x := by
  unfold besselJ
  rw [← mul_assoc, neg_div, neg_sq]
  congrm $(by simp [← mul_zpow]) * _

theorem odd_besselJ {a : ℤ} (ha : Odd a) : Function.Odd (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

theorem even_besselJ {a : ℤ} (ha : Even a) : Function.Even (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

/-- The hypergeometric part of $J_a(x)$ is analytic. -/
theorem analyticAt_besselJ_right (a x : ℂ) : AnalyticAt ℂ (fun x ↦ F₀₁(a) (- (x / 2) ^ 2)) x := by
  let f := fun (x : ℂ) ↦ - (x / 2) ^ 2
  have h1 := (S₀₁(a).hasFPowerSeriesOnBall (by simp)).analyticAt_of_mem (by simp : f x ∈ _)
  exact AnalyticAt.comp h1 (by fun_prop)

/-- $J_a(x)$ is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    AnalyticAt ℂ (J a) x := by
  refine AnalyticAt.mul ?_ (analyticAt_besselJ_right a x)
  apply AnalyticAt.cpow
  · fun_prop
  · fun_prop
  · simpa [slitPlane] using h

/-- For integer $a$, $J_a(x)$ and $J_{-a}(x)$ are related by a sign. -/
theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J (-a) x = (-1) ^ a * J a x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    simp only [Int.cast_neg, neg_neg, zpow_neg] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  push_cast
  unfold besselJ regularizedHGFun FormalMultilinearSeries.sum
  conv_lhs => rw [← (S₀₁(-a).summable (by simp)).sum_add_tsum_nat_add a]
  have : ∑ i ∈ Finset.range a, S₀₁(-a) i (fun _ ↦ - (x / 2) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    suffices C₀₁(-a) n = 0 by simp [this]
    refine regularizedHGFunCoeff_eq_zero_right _ _ _ (a - n - 1) ?_
    rw [Multiset.mem_singleton]
    norm_cast
    grind
  simp_rw [this, zero_add, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  suffices (x / 2) ^ (-a : ℂ) *
      ((-(x / 2) ^ 2) ^ (n + a) * ((Gamma (-a + 1 + (n + a)))⁻¹ * (↑(n + a)!)⁻¹)) =
      (-1) ^ a * ((x / 2) ^ a * ((-(x / 2) ^ 2) ^ n * ((Gamma (a + 1 + n))⁻¹ * (↑(n !))⁻¹))) by
    simpa [regularizedHGFunCoeff]
  have h : (x / 2) ^ a = (x / 2) ^ (-a : ℂ) * ((x / 2) ^ 2) ^ a := by
    by_cases hx : x = 0
    · by_cases ha : a = 0 <;> simp [hx, ha]
    rw [← pow_mul, ← cpow_natCast, ← cpow_natCast, ← cpow_add _ _ (by simpa using hx)]
    grind
  rw [h, pow_add, neg_pow _ a, ← Gamma_nat_eq_factorial, ← Gamma_nat_eq_factorial]
  push_cast
  ring_nf

theorem besselJ_neg_comm (a : ℤ) (x : ℂ) : J (-a) x = J a (-x) := by
  rw [besselJ_neg_int, ← besselJ_int_neg]

/-- $J_a(x)$ is analytic for integer $a$. -/
@[fun_prop]
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (J a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    convert! AnalyticAt.mul (analyticAt_const (v := ((-1) ^ a)⁻¹)) this
    ext x
    simp [besselJ_neg_int, ← mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero a (show (-1 ≠ (0 : ℂ)) by simp))]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  refine AnalyticAt.mul ?_ (analyticAt_besselJ_right a x)
  norm_cast
  fun_prop

@[simp]
theorem besselJ_zero (a : ℂ) : J a 0 = if a = 0 then 1 else 0 := by
  rw [besselJ, regularizedHGFun, regularizedHGFunSeries, ← ofScalarsSum]
  split_ifs with ha <;> simp [regularizedHGFunCoeff, ha]

end Complex
