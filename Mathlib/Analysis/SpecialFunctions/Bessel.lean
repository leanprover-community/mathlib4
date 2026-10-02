/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
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
* Bessel's integrals

-/

@[expose] public noncomputable section

open Nat FormalMultilinearSeries Topology

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

@[dlmf 10.6.E2]
theorem mul_deriv_besselJ_eq_besselJ_add_one (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x * deriv (J a) x = a * J a x - x * J (a + 1) x := by
  have hx2 : x / 2 ∈ slitPlane := by simpa [slitPlane] using h
  have hx0 : x / 2 ≠ 0 := fun h ↦ by simp_all
  unfold besselJ
  calc
    _ = x * (deriv (fun x ↦ (x / 2) ^ a) x * F₀₁(a + 1) (-(x / 2) ^ 2) +
        (x / 2) ^ a * deriv ((fun x ↦ F₀₁(a + 1) x) ∘ fun x ↦ -(x / 2) ^ 2) x) := by
      rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
      rfl
    _ = 2 * (x / 2) * deriv (fun x ↦ (x / 2) ^ a) x * F₀₁(a + 1) (-(x / 2) ^ 2) + x *
        (x / 2) ^ a * (F₀₁(a + 1 + 1) (-(x / 2) ^ 2) * (-x / 2)) := by
      rw [deriv_comp _ (by fun_prop) (by fun_prop), deriv_regularizedHGFun (by simp)]
      simp
      ring
    _ = (a * (x / 2) ^ a) * F₀₁(a + 1) (-(x / 2) ^ 2) + x *
        (x / 2) ^ a * (F₀₁(a + 1 + 1) (-(x / 2) ^ 2) * (-x / 2)) := by
      congrm ?_ * _ + _
      rw [_root_.deriv_cpow_const (by fun_prop) (by exact hx2)]
      trans 2 * a * ((x / 2) ^ (a - 1) * (x / 2) ^ (1 : ℂ) * deriv (· / 2) x)
      · norm_cast
        ring
      rw [← cpow_add _ _ hx0]
      simp
      ring
    _ = _ := by
      rw [cpow_add _ _ hx0, cpow_one]
      ring

@[dlmf 10.6.E2]
theorem mul_deriv_besselJ_eq_besselJ_sub_one (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x * deriv (J a) x = x * J (a - 1) x - a * J a x := by
  linear_combination two_mul_self_mul_besselJ a x + mul_deriv_besselJ_eq_besselJ_add_one a h

@[dlmf 10.6.E1]
theorem two_mul_deriv_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    2 * deriv (J a) x = J (a - 1) x - J (a + 1) x := by
  have hx0 : x ≠ 0 := fun h ↦ by simp_all
  rw [← mul_left_inj' hx0]
  linear_combination mul_deriv_besselJ_eq_besselJ_sub_one a h +
    mul_deriv_besselJ_eq_besselJ_add_one a h

@[dlmf 10.6.E1]
theorem two_mul_deriv_besselJ_int (a : ℤ) (x : ℂ) :
    2 * deriv (J a) x = J (a - 1) x - J (a + 1) x := by
  revert x
  rw [← funext_iff]
  apply AnalyticOnNhd.eq_of_frequently_eq (by fun_prop) (by norm_cast; fun_prop) (z₀ := 1)
  refine (eventually_nhdsWithin_of_eventually_nhds (eventually_nhds_iff.mpr ?_)).frequently
  exact ⟨slitPlane, fun x hx ↦ two_mul_deriv_besselJ a hx, isOpen_slitPlane, by simp⟩

@[dlmf 10.6.E2]
theorem mul_deriv_besselJ_eq_besselJ_add_one_int (a : ℤ) (x : ℂ) :
    x * deriv (J a) x = a * J a x - x * J (a + 1) x := by
  linear_combination x * two_mul_deriv_besselJ_int a x / 2 - two_mul_self_mul_besselJ a x / 2

@[dlmf 10.6.E2]
theorem mul_deriv_besselJ_eq_besselJ_sub_one_int (a : ℤ) (x : ℂ) :
    x * deriv (J a) x = x * J (a - 1) x - a * J a x := by
  linear_combination two_mul_self_mul_besselJ a x + mul_deriv_besselJ_eq_besselJ_add_one_int a x

theorem norm_besselJ_le_exp {a : ℂ} (ha : 0 ≤ a.re) (x : ℂ) :
    ‖J a x‖ ≤ ‖Gamma (a + 1)‖⁻¹ * ‖(x / 2) ^ a‖ * Real.exp (‖x / 2‖ ^ 2) := by
  unfold besselJ
  grw [norm_mul, regularizedHGFun_le_exp_of_one_le_re (by simpa using ha)]
  apply le_of_eq
  simp
  ring

theorem norm_besselJ_le_exp_int (a : ℤ) (x : ℂ) :
    ‖J a x‖ ≤ (a.natAbs ! : ℝ)⁻¹ * ‖x / 2‖ ^ a.natAbs * Real.exp (‖x / 2‖ ^ 2) := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) (-x) (by simpa using ha.le)
    simpa [besselJ_neg_comm] using this
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  grw [norm_besselJ_le_exp (by simp)]
  simp [Gamma_nat_eq_factorial]

-- Within a bounded set, `J a x * t ^ a` can be bounded uniformly by exp series terms.
private theorem besselJ_mul_pow_le (t : ℂ) {s : Set ℂ} (hs : Bornology.IsBounded s) :
    ∃ u v, ∀ a : ℤ, ∀ x ∈ s,
      ‖J a x * t ^ a‖ ≤ (a.natAbs ! : ℝ)⁻¹ * (u ^ a.natAbs * ‖t ^ a‖) * v := by
  obtain ⟨x, hx⟩ := hs.exists_norm_le
  refine ⟨‖x / 2‖, Real.exp (‖x / 2‖ ^ 2), fun a y hy ↦ ?_⟩
  have hy' : ‖y / 2‖ ≤ ‖x / 2‖ := by
    grw [norm_div, hx y hy, le_abs_self x]
    simp
  grw [norm_mul, norm_besselJ_le_exp_int, hy', hy']
  exact le_of_eq (by ring)

-- The uniform bound on `J a x * t ^ a` is summable
private theorem summable_bound (u v : ℝ) (t : ℂ) :
    Summable fun a : ℤ ↦ (a.natAbs ! : ℝ)⁻¹ * (u ^ a.natAbs * ‖t ^ a‖) * v := by
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
  · simpa [mul_pow] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (u * ‖t‖)).summable.mul_right v
  · simpa [mul_pow] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (u * ‖t‖⁻¹)).summable.mul_right v

theorem analyticOnNhd_tsum_besselJ_mul_pow (t : ℂ) :
    AnalyticOnNhd ℂ (∑' a : ℤ, J a · * t ^ a) Set.univ := by
  refine (analyticOnNhd_iff_differentiableOn isOpen_univ).mpr fun x _ ↦ ?_
  obtain ⟨u, v, h⟩ := besselJ_mul_pow_le t (Metric.isBounded_ball (x := x) (r := 1))
  exact differentiableOn_tsum_of_summable_norm (summable_bound u v t)
    (fun _ _ _ ↦ AnalyticAt.differentiableWithinAt (by fun_prop)) Metric.isOpen_ball h
    |>.differentiableAt (Metric.ball_mem_nhds _ (by simp)) |>.differentiableWithinAt

theorem summable_besselJ_mul_pow (x : ℂ) (t : ℂ) : Summable (fun a : ℤ ↦ J a x * t ^ a) := by
  obtain ⟨u, v, h⟩ := besselJ_mul_pow_le t (Bornology.isBounded_singleton (x := x))
  exact (summable_bound u v t).of_norm_bounded fun a ↦ h a x (Set.mem_singleton x)

@[dlmf 10.12.E1]
theorem tsum_besselJ_mul_pow (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    ∑' a : ℤ, J a x * t ^ a = exp (x / 2 * (t - t⁻¹)) := by
  -- It suffices to prove the equality in a ball at `x = 0` where LHS is non-zero
  have : ∀ᶠ x in nhds 0, ∑' a : ℤ, J a x * t ^ a ≠ 0 := by
    apply (analyticOnNhd_tsum_besselJ_mul_pow t).continuous.continuousAt.eventually_ne
    simp [besselJ_zero]
  obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp this
  revert x
  rw [← funext_iff]
  refine (analyticOnNhd_tsum_besselJ_mul_pow t).eq_of_eventuallyEq (fun x hx ↦ by fun_prop)
    (Metric.eventually_nhds_iff_ball.mpr ⟨r, hr0, ?_⟩) (z₀ := 0)
  -- It suffices to prove that both sides agree on `logDeriv`, because they agree at `x = 0`
  suffices Set.EqOn (logDeriv fun x ↦ ∑' a : ℤ, J a x * t ^ a)
      (logDeriv fun x ↦ exp (x / 2 * (t - t⁻¹))) (Metric.ball 0 r) by
    obtain ⟨k, hk0, hk⟩ := logDeriv_eqOn_iff
      ((analyticOnNhd_tsum_besselJ_mul_pow t).differentiableOn.mono (by simp))
      (by fun_prop) Metric.isOpen_ball Metric.isPreconnected_ball (by simp) hr |>.mp this
    have hk1 : k = 1 := by simpa [besselJ_zero] using (hk (show 0 ∈ _ by simpa using hr0)).symm
    simpa [hk1, Set.EqOn] using hk
  -- Show both sides are `(t - t⁻¹) / 2`
  intro x hx
  calc
    _ = deriv (∑' a : ℤ, J a · * t ^ a) x / ∑' a : ℤ, J a x * t ^ a := by rw [logDeriv_apply]
    _ = (∑' a : ℤ, deriv (J a · * t ^ a) x) / ∑' a : ℤ, J a x * t ^ a := by
      obtain ⟨u, v, h⟩ := besselJ_mul_pow_le t (Metric.isBounded_ball (x := 0) (r := r))
      rw [hasSum_deriv_of_summable_norm (summable_bound u v t)
        (fun _ _ _ ↦ AnalyticAt.differentiableWithinAt (by fun_prop)) Metric.isOpen_ball h hx
        |>.tsum_eq]
    _ = (∑' a : ℤ, (J (a - 1) x - J (a + 1) x) * t ^ a) / 2 / ∑' a : ℤ, J a x * t ^ a := by
      simp [← two_mul_deriv_besselJ_int, ← tsum_div_const, mul_assoc]
    _ = (∑' a : ℤ, (J (a - 1) x * t ^ (a - 1) * t - J (a + 1) x * t ^ (a + 1) * t⁻¹)) /
        2 / ∑' a : ℤ, J a x * t ^ a := by
      simp_rw [sub_mul, ← zpow_neg_one, mul_assoc, ← zpow_add_one₀ ht, ← zpow_add₀ ht]
      simp
    _ = ((∑' a : ℤ, J (a - 1) x * t ^ (a - 1)) * t - (∑' a : ℤ, J (a + 1) x * t ^ (a + 1)) * t⁻¹) /
        2 / ∑' a : ℤ, J a x * t ^ a := by
      rw [Summable.tsum_sub ?_ ?_]
      · simp_rw [tsum_mul_right]
      · simpa using ((Equiv.subRight 1).summable_iff.mpr (summable_besselJ_mul_pow x t)).mul_right t
      · simpa using ((Equiv.addRight 1).summable_iff.mpr
          (summable_besselJ_mul_pow x t)).mul_right t⁻¹
    _ = ((∑' a : ℤ, J a x * t ^ a) * t - (∑' a : ℤ, J a x * t ^ a) * t⁻¹) /
        2 / ∑' a : ℤ, J a x * t ^ a := by
      congrm (?_ * _ - ?_ * _) / _ / _
      · simpa using (Equiv.subRight 1).tsum_eq (fun a : ℤ ↦ J a x * t ^ a)
      · simpa using (Equiv.addRight 1).tsum_eq (fun a : ℤ ↦ J a x * t ^ a)
    _ = (t - t⁻¹) / 2 := by field [hr x hx]
    _ = _ := by
      rw [logDeriv_apply, deriv_cexp (by fun_prop)]
      simp [field]

theorem hasSum_besselJ_mul_pow (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun a : ℤ ↦ J a x * t ^ a) (exp (x / 2 * (t - t⁻¹))) :=
  (summable_besselJ_mul_pow x t).hasSum_iff.mpr (tsum_besselJ_mul_pow x ht)

end Complex
