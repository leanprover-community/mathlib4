/-
Copyright (c) 2026 Uwe Brauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uwe Brauer
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination

/-!
# Grönwall's inequality with a variable coefficient

This file proves Grönwall's inequality in differential form with a variable coefficient `K`
and a variable inhomogeneous term `ε`, both of arbitrary sign, for a function with right
derivatives. If `f : ℝ → ℝ` is continuous on `[a, b]`, has right derivative `f' t` at every
`t ∈ [a, b)`, satisfies `f' t ≤ K t * f t + ε t` there, and `f a ≤ δ`, then for all
`t ∈ [a, b]` we have `f t ≤ gronwallBoundVar δ K ε a t`, where `gronwallBoundVar δ K ε a t` is
`(δ + ∫ s in a..t, ε s / exp (∫ r in a..s, K r)) * exp (∫ s in a..t, K s)`.

The Grönwall-like inequality `le_gronwallBound_of_liminf_deriv_right_le` in
`Mathlib/Analysis/ODE/Gronwall.lean` assumes a constant coefficient `K` and a constant
inhomogeneous term `ε`; its TODO asks for a variable coefficient `K x` of any sign. For
constants `K` and `ε`, `gronwallBoundVar` reduces to `gronwallBound δ K ε (t - a)`.

## Main definitions

* `gronwallBoundVar δ K ε a t`: the bound above.

## Main results

* `le_gronwallBoundVar_of_deriv_right_le`: Grönwall's inequality with a variable coefficient.
* `gronwallBoundVar_const`: for constants `K` and `ε`, `gronwallBoundVar` is
  `gronwallBound`.
* `le_mul_exp_integral_of_deriv_right_le_mul`: the homogeneous case `ε = 0`,
  `f t ≤ δ * exp (∫ s in a..t, K s)`.

Auxiliary results:

* `continuousOn_primitive_of_continuousOn`: the primitive `t ↦ ∫ s in a..t, φ s` of a
  function continuous on `[a, b]` is continuous on `[a, b]`.
* `hasDerivWithinAt_Ici_primitive`: for `t ∈ [a, b)` this primitive has right derivative
  `φ t` at `t` (fundamental theorem of calculus, one-sided version).

## Implementation notes

The hypotheses follow `norm_le_gronwallBound_of_norm_deriv_right_le`: continuity on `[a, b]`
and right derivatives on `[a, b)`. The proof uses the integrating factor
`v t = exp (∫ s in a..t, K s)` and the primitive `H` of `ε / v` with `H a = 0`. The function
`G = f / v - H` has non-positive right derivative `(f' - K * f - ε) / v` on `[a, b)`, so the
comparison lemma `image_le_of_deriv_right_le_deriv_boundary` gives `G t ≤ G a = f a ≤ δ`;
multiplying by `v t > 0` gives the bound.

## TODO

* Weaken the hypothesis on `f` to a bound on the lower right Dini derivative, as in
  `le_gronwallBound_of_liminf_deriv_right_le`.
* Prove the version for `‖f‖` with `f` vector-valued, `‖f' t‖ ≤ K t * ‖f t‖ + ε t`.
* State the bound also in the form
  `δ * exp (∫ s in a..t, K s) + ∫ s in a..t, ε s * exp (∫ r in s..t, K r)`,
  and the simplified version for `0 ≤ K` and `0 ≤ ε`.
* Prove the energy form of [Bahouri, Chemin, Danchin, *Fourier Analysis and Nonlinear Partial
  Differential Equations*, Lemma 3.3][Bahouri_Chemin_Danchin_2011], with the hypothesis
  `(1/2) * (g ^ 2)' ≤ A * g ^ 2 + f * g`, as a corollary (`K = 0` and an `η`-regularisation).

## References

* [H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*][Bahouri_Chemin_Danchin_2011]

## Tags

Grönwall's inequality, Gronwall, differential inequality, integrating factor
-/

@[expose] public section

open Set Filter Topology intervalIntegral MeasureTheory

/-- The bound in Grönwall's inequality with a variable coefficient `K` and a variable
inhomogeneous term `ε`, for the initial bound `δ` at the point `a`:
`(δ + ∫ s in a..t, ε s / exp (∫ r in a..s, K r)) * exp (∫ s in a..t, K s)`. -/
noncomputable def gronwallBoundVar (δ : ℝ) (K ε : ℝ → ℝ) (a t : ℝ) : ℝ :=
  (δ + ∫ s in a..t, ε s / Real.exp (∫ r in a..s, K r)) * Real.exp (∫ s in a..t, K s)

/-- If `φ` is continuous on `[a, b]` and `a ≤ b`, then its primitive `t ↦ ∫ s in a..t, φ s`
is continuous on `[a, b]`. -/
theorem continuousOn_primitive_of_continuousOn {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) :
    ContinuousOn (fun t ↦ ∫ s in a..t, φ s) (Icc a b) := by
  have e : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntegrableOn φ (uIcc a b) volume := by
    rw [e]
    exact hφ.integrableOn_compact isCompact_Icc
  have h := continuousOn_primitive_interval hint
  rw [e] at h
  exact h

/-- **Fundamental theorem of calculus**, one-sided version: if `φ` is continuous on `[a, b]`,
then for every `t ∈ [a, b)` the primitive `y ↦ ∫ s in a..y, φ s` has right derivative `φ t`
at `t`. -/
theorem hasDerivWithinAt_Ici_primitive {a b t : ℝ} {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun y ↦ ∫ s in a..y, φ s) (φ t) (Ici t) t := by
  have hat : a ≤ t := ht.1
  have htb : t < b := ht.2
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  -- φ is integrable on [a, t] ⊆ [a, b]
  have hφ_at : ContinuousOn φ (Icc a t) := hφ.mono (Icc_subset_Icc_right htb.le)
  have hint : IntervalIntegrable φ volume a t := hφ_at.intervalIntegrable_of_Icc hat
  -- the remaining hypotheses of the fundamental theorem of calculus
  have : Fact (t ∈ Icc a b) := Fact.mk ht'
  have hmeas : StronglyMeasurableAtFilter φ (𝓝[Icc a b] t) :=
    hφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  have hcont : ContinuousWithinAt φ (Icc a b) t := hφ t ht'
  -- FTC: derivative within [a, b]
  have h : HasDerivWithinAt (fun y ↦ ∫ s in a..y, φ s) (φ t) (Icc a b) t :=
    integral_hasDerivWithinAt_right hint hmeas hcont
  -- [a, b] is a right neighbourhood of t (as t < b): this is the right derivative
  have hnhds : Icc a b ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht
  exact h.mono_of_mem_nhdsWithin hnhds

/-- **Grönwall's inequality** with a variable coefficient: let `K` and `ε` be continuous on
`[a, b]`, and let `f` be continuous on `[a, b]` with right derivative `f' t` at every
`t ∈ [a, b)`, such that `f' t ≤ K t * f t + ε t` for `t ∈ [a, b)` and `f a ≤ δ`. Then
`f t ≤ gronwallBoundVar δ K ε a t` for all `t ∈ [a, b]`.

There are no sign conditions on `K`, `ε` or `f`. For constants `K` and `ε` the bound is
`gronwallBound δ K ε (t - a)` (`gronwallBoundVar_const`), the bound of
`le_gronwallBound_of_liminf_deriv_right_le`. -/
theorem le_gronwallBoundVar_of_deriv_right_le {f f' K ε : ℝ → ℝ} {δ a b : ℝ}
    (hK : ContinuousOn K (Icc a b)) (hε : ContinuousOn ε (Icc a b))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (ha : f a ≤ δ) (bound : ∀ t ∈ Ico a b, f' t ≤ K t * f t + ε t) :
    ∀ t ∈ Icc a b, f t ≤ gronwallBoundVar δ K ε a t := by
  intro t ht
  unfold gronwallBoundVar
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have hab : a ≤ b := le_trans hat htb
  -- the integrating factor `v`
  set v : ℝ → ℝ := fun y ↦ Real.exp (∫ s in a..y, K s) with hv_def
  have hv_pos : ∀ y, 0 < v y := by
    intro y
    exact Real.exp_pos (∫ s in a..y, K s)
  have hv_ne : ∀ y, v y ≠ 0 := by
    intro y
    exact (hv_pos y).ne'
  have hva : v a = 1 := by simp [hv_def]
  have hv_cont : ContinuousOn v (Icc a b) :=
    (continuousOn_primitive_of_continuousOn hab hK).rexp
  have hv' : ∀ y ∈ Ico a b, HasDerivWithinAt v (v y * K y) (Ici y) y := by
    intro y hy
    exact (hasDerivWithinAt_Ici_primitive hK hy).exp
  -- the primitive `H` of `w = ε / v`
  set w : ℝ → ℝ := fun s ↦ ε s / v s with hw_def
  have hw_cont : ContinuousOn w (Icc a b) := hε.div hv_cont (fun y _hy ↦ hv_ne y)
  set H : ℝ → ℝ := fun y ↦ ∫ s in a..y, w s with hH_def
  have hH_cont : ContinuousOn H (Icc a b) := continuousOn_primitive_of_continuousOn hab hw_cont
  have hH' : ∀ y ∈ Ico a b, HasDerivWithinAt H (w y) (Ici y) y := by
    intro y hy
    exact hasDerivWithinAt_Ici_primitive hw_cont hy
  -- the non-increasing function `G = f / v - H`
  set G : ℝ → ℝ := fun y ↦ f y / v y - H y with hG_def
  have hfv_cont : ContinuousOn (fun y ↦ f y / v y) (Icc a b) :=
    hf.div hv_cont (fun y _hy ↦ hv_ne y)
  have hG_cont : ContinuousOn G (Icc a b) := hfv_cont.sub hH_cont
  have hG' : ∀ y ∈ Ico a b,
      HasDerivWithinAt G ((f' y * v y - f y * (v y * K y)) / v y ^ 2 - w y) (Ici y) y := by
    intro y hy
    -- quotient rule for f / v
    have hq : HasDerivWithinAt (fun x ↦ f x / v x)
        ((f' y * v y - f y * (v y * K y)) / v y ^ 2) (Ici y) y :=
      (hf' y hy).div (hv' y hy) (hv_ne y)
    -- difference rule for f / v - H
    exact hq.sub (hH' y hy)
  have hbound : ∀ y ∈ Ico a b,
      (f' y * v y - f y * (v y * K y)) / v y ^ 2 - w y ≤ 0 := by
    intro y hy
    have hvy : 0 < v y := hv_pos y
    rw [sub_nonpos]
    change (f' y * v y - f y * (v y * K y)) / v y ^ 2 ≤ ε y / v y
    rw [div_le_div_iff₀ (pow_pos hvy 2) hvy]
    have key : f' y - K y * f y ≤ ε y := by linarith [bound y hy]
    calc (f' y * v y - f y * (v y * K y)) * v y
        = v y ^ 2 * (f' y - K y * f y) := by ring
      v y ^ 2 * (f' y - K y * f y) ≤ v y ^ 2 * ε y :=
        mul_le_mul_of_nonneg_left key (sq_nonneg (v y))
      v y ^ 2 * ε y = ε y * v y ^ 2 := by ring
  have hGa : G a = f a := by simp [hG_def, hH_def, hva]
  -- comparison with the constant function `f a`, whose derivative is `0`
  have hB_cont : ContinuousOn (fun _x ↦ f a) (Icc a b) := continuousOn_const
  have hB' : ∀ y ∈ Ico a b, HasDerivWithinAt (fun _x ↦ f a) 0 (Ici y) y := by
    intro y _hy
    exact hasDerivWithinAt_const y (Ici y) (f a)
  have hcomp := image_le_of_deriv_right_le_deriv_boundary
    (B := fun _x ↦ f a) (B' := fun _x ↦ 0)
    hG_cont hG' hGa.le hB_cont hB' hbound
  have h1 : G t ≤ f a := hcomp ht
  have hGt : G t = f t / v t - H t := rfl
  have h2 : f t / v t ≤ δ + H t := by linarith
  exact (div_le_iff₀ (hv_pos t)).mp h2

/-- For a constant coefficient `K` and a constant inhomogeneous term `ε`,
`gronwallBoundVar` is the bound `gronwallBound` of `Mathlib/Analysis/ODE/Gronwall.lean`. -/
theorem gronwallBoundVar_const {δ K ε a t : ℝ} :
    gronwallBoundVar δ (fun _x ↦ K) (fun _x ↦ ε) a t = gronwallBound δ K ε (t - a) := by
  by_cases hK : K = 0
  · -- `K = 0`: both bounds are `δ + ε * (t - a)`
    subst hK
    simp only [gronwallBoundVar, intervalIntegral.integral_const, smul_eq_mul, mul_zero,
      Real.exp_zero, div_one, mul_one, gronwallBound_K0]
    ring
  -- `K ≠ 0`
  -- an antiderivative of `s ↦ ε / exp ((s - a) * K)`
  have hF : ∀ s, HasDerivAt (fun s ↦ -(ε / K) * Real.exp (-((s - a) * K)))
      (ε / Real.exp ((s - a) * K)) s := by
    intro s
    have h0 : HasDerivAt (fun s ↦ (s - a) * K) (1 * K) s :=
      ((hasDerivAt_id s).sub_const a).mul_const K
    rw [one_mul] at h0
    have h1 : HasDerivAt (fun s ↦ -((s - a) * K)) (-K) s := h0.neg
    have h2 := h1.exp.const_mul (-(ε / K))
    have hderiv : -(ε / K) * (Real.exp (-((s - a) * K)) * -K) = ε / Real.exp ((s - a) * K) := by
      rw [Real.exp_neg]
      have hKinv : K⁻¹ * K = 1 := inv_mul_cancel₀ hK
      linear_combination (ε * (Real.exp ((s - a) * K))⁻¹) * hKinv
    exact h2.congr_deriv hderiv
  -- the integrand is continuous, hence integrable
  have hcont : Continuous (fun s ↦ ε / Real.exp ((s - a) * K)) :=
    continuous_const.div₀ (by fun_prop) (fun s ↦ Real.exp_ne_zero ((s - a) * K))
  -- fundamental theorem of calculus
  have hI : ∫ s in a..t, ε / Real.exp ((s - a) * K) =
      -(ε / K) * Real.exp (-((t - a) * K)) - -(ε / K) * Real.exp (-((a - a) * K)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _hs ↦ hF s)
      (hcont.intervalIntegrable a t)
  -- unfold both bounds; the integrals of the constant `K` are `(s - a) * K`
  simp only [gronwallBoundVar, intervalIntegral.integral_const, smul_eq_mul,
    gronwallBound_of_K_ne_0 hK]
  rw [hI, sub_self, zero_mul, neg_zero, Real.exp_zero, Real.exp_neg, mul_comm K (t - a)]
  have hE : (Real.exp ((t - a) * K))⁻¹ * Real.exp ((t - a) * K) = 1 :=
    inv_mul_cancel₀ (Real.exp_ne_zero ((t - a) * K))
  linear_combination (-(ε / K)) * hE

/-- Homogeneous case `ε = 0`: if `f' t ≤ K t * f t` on `[a, b)` and `f a ≤ δ`, then
`f t ≤ δ * exp (∫ s in a..t, K s)` on `[a, b]`. -/
theorem le_mul_exp_integral_of_deriv_right_le_mul {f f' K : ℝ → ℝ} {δ a b : ℝ}
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (ha : f a ≤ δ) (bound : ∀ t ∈ Ico a b, f' t ≤ K t * f t) :
    ∀ t ∈ Icc a b, f t ≤ δ * Real.exp (∫ s in a..t, K s) := by
  intro t ht
  have bound0 : ∀ y ∈ Ico a b, f' y ≤ K y * f y + (fun _x ↦ (0 : ℝ)) y := by
    intro y hy
    simpa using bound y hy
  have h := le_gronwallBoundVar_of_deriv_right_le (ε := fun _x ↦ 0)
    hK continuousOn_const hf hf' ha bound0 t ht
  have hB : gronwallBoundVar δ K (fun _x ↦ 0) a t = δ * Real.exp (∫ s in a..t, K s) := by
    simp [gronwallBoundVar]
  rw [hB] at h
  exact h

end
