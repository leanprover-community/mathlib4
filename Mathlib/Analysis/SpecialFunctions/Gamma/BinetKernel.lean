/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum.NatFactorial


/-!
# The Binet Kernel Function

This file analyzes the kernel function `K(t) = 1/(exp t - 1) - 1/t + 1/2` that appears in Binet's
integral representation of `log Γ`.

## Main results

* `BinetKernel.tendsto_Ktilde_zero`: `Ktilde t → 1/12` as `t → 0⁺`
* `BinetKernel.K_nonneg`: `0 ≤ K t` for `t > 0`
* `BinetKernel.Ktilde_le`: `Ktilde t ≤ 1/12` for `t ≥ 0`
* `BinetKernel.integrable_Ktilde_exp_complex`: integrability of `t ↦ Ktilde t * exp(-t*z)` on
  `(0, ∞)` for `0 < z.re`
* `BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve`:
  Robbins-type lower bound `(1/12) * exp(-t/12) ≤ Ktilde t` for `t > 0`

## Mathematical background

The function 1/(e^t - 1) has the Laurent expansion at t = 0:
  1/(e^t - 1) = 1/t - 1/2 + t/12 - t³/720 + ...

Therefore (formally, via Taylor expansions):
  K(t) = 1/(e^t - 1) - 1/t + 1/2
       = (1/t - 1/2 + t/12 - t³/720 + ...) - 1/t + 1/2
       = t/12 - t³/720 + O(t⁵)

This shows K(t) → 0 as t → 0⁺. The normalized Binet kernel is:
  K̃(t) = K(t) / t = (1/(e^t - 1) - 1/t + 1/2) / t for t > 0

which satisfies K̃(t) → 1/12 as t → 0⁺.

-/

open Real Set Filter MeasureTheory Topology
open scoped Topology

namespace BinetKernel

/-! ### General monotonicity and positivity lemmas -/

/-- If a function has nonnegative derivative on `[0, ∞)`, it is monotone there. -/
private lemma monotoneOn_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) :
    MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuousOn (hf.mono interior_subset)
  intro x hx
  rw [interior_Ici] at hx
  exact hderiv x (Set.mem_Ici.mpr (le_of_lt hx))

/-- If `deriv f ≥ 0` on `[0, ∞)` and `f 0 = 0`, then `f x ≥ 0` for `x ≥ 0`. -/
private lemma nonneg_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) (h0 : f 0 = 0) :
    ∀ {x}, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono := monotoneOn_of_deriv_nonneg_Ici hf hderiv
  have hx' : x ∈ Set.Ici 0 := hx
  have h0' : (0 : ℝ) ∈ Set.Ici 0 := by simp
  have hle := hmono h0' hx' hx
  simpa [h0] using hle

/-! ## Basic definitions and elementary properties -/

/-- The (unnormalized) Binet kernel.

We define `K : ℝ → ℝ` on all of `ℝ` by setting `K t = 0` for `t ≤ 0`, and using
`K(t) = 1/(exp t - 1) - 1/t + 1/2` for `t > 0`.
This total definition is convenient for global boundedness/continuity statements; the analytic
content is on `(0, ∞)`. -/
noncomputable def K (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else 1/(Real.exp t - 1) - 1/t + 1/2

/-- The normalized Binet kernel.

We define `Ktilde : ℝ → ℝ` by setting `Ktilde t = 1/12` for `t ≤ 0`, and
`Ktilde(t) = (1/(exp t - 1) - 1/t + 1/2) / t` for `t > 0`.
The value `1/12` is the right-limit as `t → 0⁺`. -/
noncomputable def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1/12 else (1/(Real.exp t - 1) - 1/t + 1/2) / t

/-- For t > 0, K has the explicit formula. -/
lemma K_pos {t : ℝ} (ht : 0 < t) : K t = 1/(Real.exp t - 1) - 1/t + 1/2 := by
  simp [K, not_le.mpr ht]

/-- For t > 0, K̃ has the explicit formula. -/
lemma Ktilde_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1/(Real.exp t - 1) - 1/t + 1/2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
lemma Ktilde_zero : Ktilde 0 = 1/12 := by simp [Ktilde]

/-! ## Section 2: The key identity for the kernel -/

/-- For t > 0, e^t > 1, so e^t - 1 > 0. -/
private lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have h1 : Real.exp 0 = 1 := Real.exp_zero
  have h2 : Real.exp t > Real.exp 0 := Real.exp_lt_exp.mpr ht
  linarith

/-- K̃ is continuous on (0, ∞). -/
lemma continuousOn_Ktilde_Ioi : ContinuousOn Ktilde (Set.Ioi 0) := by
  intro t ht
  have hne_t : t ≠ 0 := ne_of_gt ht
  have hne_exp : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have h1 : ContinuousAt (fun x => 1 / (Real.exp x - 1)) t :=
    continuousAt_const.div (Real.continuous_exp.continuousAt.sub continuousAt_const) hne_exp
  have h2 : ContinuousAt (fun x => 1 / x) t := continuousAt_const.div continuousAt_id hne_t
  have h3 : ContinuousAt (fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) t :=
    (h1.sub h2).add continuousAt_const
  have h4 : ContinuousAt (fun x => (1 / (Real.exp x - 1) - 1 / x + 1 / 2) / x) t :=
    h3.div continuousAt_id hne_t
  apply h4.continuousWithinAt.congr
  · intro y hy
    unfold Ktilde
    rw [if_neg (not_le.mpr hy)]
  · unfold Ktilde
    rw [if_neg (not_le.mpr ht)]

/-- Key algebraic identity: For t > 0,
  K(t) = 1/(e^t - 1) - 1/t + 1/2 = (t - (e^t - 1) + t(e^t - 1)/2) / (t(e^t - 1))
This helps analyze the sign and bounds. -/
private lemma K_eq_alt {t : ℝ} (ht : 0 < t) :
    K t = (t - (Real.exp t - 1) + t * (Real.exp t - 1) / 2) / (t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp

/-- Alternative form: K(t) = (e^t(t-2) + t + 2) / (2t(e^t - 1)) -/
private lemma K_eq_alt' {t : ℝ} (ht : 0 < t) :
    K t = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp
  ring

/-! ## Sign analysis -/

/-- The function f(t) = e^t(t-2) + t + 2 that appears in the numerator. -/
private noncomputable def f (t : ℝ) : ℝ := Real.exp t * (t - 2) + t + 2

private lemma f_zero : f 0 = 0 := by simp [f]

/-- The derivative of f(t) = e^t(t-2) + t + 2 is f'(t) = e^t(t-1) + 1. -/
private lemma f_deriv (t : ℝ) : HasDerivAt f (Real.exp t * (t - 1) + 1) t := by
  unfold f
  have h1 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun x => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
  have h3 : HasDerivAt (fun x => Real.exp x * (x - 2)) (Real.exp t * (t - 2) + Real.exp t * 1) t :=
    h1.mul h2
  have h4 : HasDerivAt (fun x => x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have h5 := h3.add h4
  convert h5 using 1
  · ext x; simp only [Pi.add_apply]; ring
  · ring

private lemma f_deriv' (t : ℝ) : deriv f t = Real.exp t * (t - 1) + 1 :=
  (f_deriv t).deriv

/-- f has a minimum at t = 1, where f(1) = 3 - e. -/
private lemma f_at_one : f 1 = 3 - Real.exp 1 := by simp [f]; ring

/-- e < 3, so f(1) = 3 - e > 0. -/
private lemma f_one_pos : 0 < f 1 := by
  rw [f_at_one]
  have h : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/-- For t > 0, e^t(1-t) < 1. This is because g(t) = e^t(1-t) is strictly decreasing
with g(0) = 1, so g(t) < 1 for t > 0.

Proof: g'(t) = e^t(1-t) + e^t(-1) = e^t(-t) = -te^t < 0 for t > 0.
By MVT: g(t) - g(0) = g'(c) * t < 0 for some c ∈ (0, t), so g(t) < g(0) = 1. -/
private lemma exp_mul_one_sub_lt_one {t : ℝ} (ht : 0 < t) : Real.exp t * (1 - t) < 1 := by
  have hg_deriv : ∀ s, HasDerivAt (fun x => Real.exp x * (1 - x)) (-Real.exp s * s) s := by
    intro s
    have h1 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have h2 : HasDerivAt (fun x => 1 - x) (-1) s := by
      have := (hasDerivAt_const s 1).sub (hasDerivAt_id s)
      simp only at this
      convert this using 1; ring
    have h3 := h1.mul h2
    convert h3 using 1; ring
  have hg_mono : StrictAntiOn (fun x => Real.exp x * (1 - x)) (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact (Real.continuous_exp.mul (continuous_const.sub continuous_id)).continuousOn
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hg_deriv x).deriv]
      have hexp_pos : 0 < Real.exp x := Real.exp_pos x
      nlinarith
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
  have ht' : t ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_of_lt ht)
  have := hg_mono h0 ht' ht
  simp at this
  linarith

/-- f'(t) > 0 for t > 0. -/
private lemma f_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv f t := by
  rw [f_deriv' t]
  have h : Real.exp t * (1 - t) < 1 := exp_mul_one_sub_lt_one ht
  have : Real.exp t * (t - 1) = -(Real.exp t * (1 - t)) := by ring
  linarith

/-- f(t) ≥ 0 for all t ≥ 0. -/
private lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [f_zero]
  · have hf_diff : Differentiable ℝ f := fun x => (f_deriv x).differentiableAt
    have h_pos_deriv : ∀ x ∈ Set.Ioo 0 t, 0 < deriv f x := fun x hx => f_deriv_pos hx.1
    have h_mono := strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (hf_diff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
    have h0 : (0 : ℝ) ∈ Set.Icc 0 t := left_mem_Icc.mpr (le_of_lt hpos)
    have ht' : t ∈ Set.Icc 0 t := right_mem_Icc.mpr (le_of_lt hpos)
    have := h_mono h0 ht' hpos
    rw [f_zero] at this
    exact le_of_lt this

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_alt' ht]
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
  apply div_nonneg _ hdenom.le
  exact f_nonneg (le_of_lt ht)

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]; norm_num
  · rw [Ktilde_pos hpos]
    have hK : 0 ≤ K t := K_nonneg hpos
    rw [K_pos hpos] at hK
    exact div_nonneg hK (le_of_lt hpos)

/-! ## Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
private noncomputable def gAux (t : ℝ) : ℝ := (t^2 - 6*t + 12) * Real.exp t - (t^2 + 6*t + 12)

/-- First derivative: g'(t) = (t² - 4t + 6)e^t - (2t + 6) -/
private noncomputable def gAux' (t : ℝ) : ℝ := (t^2 - 4*t + 6) * Real.exp t - (2*t + 6)

/-- Second derivative: g''(t) = (t² - 2t + 2)e^t - 2 -/
private noncomputable def gAux'' (t : ℝ) : ℝ := (t^2 - 2*t + 2) * Real.exp t - 2

/-- Third derivative: g'''(t) = t²e^t -/
private noncomputable def gAux''' (t : ℝ) : ℝ := t^2 * Real.exp t

private lemma gAux_zero : gAux 0 = 0 := by simp [gAux]

private lemma gAux'_zero : gAux' 0 = 0 := by simp [gAux']

private lemma gAux''_zero : gAux'' 0 = 0 := by simp [gAux'']

/-- g'''(t) = t²e^t ≥ 0 for all t ≥ 0. -/
private lemma gAux'''_nonneg {t : ℝ} (_ht : 0 ≤ t) : 0 ≤ gAux''' t := by
  simp only [gAux''']
  exact mul_nonneg (sq_nonneg t) (Real.exp_pos t).le

private lemma gAux'''_pos {t : ℝ} (ht : 0 < t) : 0 < gAux''' t := by
  simp [gAux''', sq_pos_of_ne_zero (ne_of_gt ht), Real.exp_pos]

/-! #### Derivative relations for the `gAux` hierarchy -/

/-- g'' has derivative g''' -/
private lemma hasDerivAt_gAux'' (t : ℝ) : HasDerivAt gAux'' (gAux''' t) t := by
  unfold gAux'' gAux'''
  have h1 : HasDerivAt (fun x => x^2 - 2*x + 2) (2*t - 2) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 2)
    convert this.add (hasDerivAt_const t 2) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x - 2)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t - 0) t :=
    h3.sub (hasDerivAt_const t 2)
  simp only [sub_zero] at h4
  convert h4 using 1
  ring

/-- g' has derivative g'' -/
private lemma hasDerivAt_gAux' (t : ℝ) : HasDerivAt gAux' (gAux'' t) t := by
  unfold gAux' gAux''
  have h1 : HasDerivAt (fun x => x^2 - 4*x + 6) (2*t - 4) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 4)
    convert this.add (hasDerivAt_const t 6) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x)
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => 2*x + 6) 2 t := by
    convert (hasDerivAt_id t).const_mul 2 |>.add (hasDerivAt_const t 6) using 1
    ring
  have h5 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x - (2*x + 6))
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t - 2) t := h3.sub h4
  convert h5 using 1
  ring

/-- g has derivative g' -/
private lemma hasDerivAt_gAux (t : ℝ) : HasDerivAt gAux (gAux' t) t := by
  unfold gAux gAux'
  have h1 : HasDerivAt (fun x => x^2 - 6*x + 12) (2*t - 6) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x)
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => x^2 + 6*x + 12) (2*t + 6) t := by
    have := (hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h5 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x - (x^2 + 6*x + 12))
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t - (2*t + 6)) t := h3.sub h4
  convert h5 using 1
  ring

/-! #### Non-negativity proofs for the `gAux` hierarchy -/

/-- g'' is differentiable on [0, ∞) -/
private lemma differentiableOn_gAux'' : DifferentiableOn ℝ gAux'' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_gAux'' x).differentiableAt.differentiableWithinAt

/-- g' is differentiable on [0, ∞) -/
private lemma differentiableOn_gAux' : DifferentiableOn ℝ gAux' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_gAux' x).differentiableAt.differentiableWithinAt

/-- g is differentiable on [0, ∞) -/
private lemma differentiableOn_gAux : DifferentiableOn ℝ gAux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_gAux x).differentiableAt.differentiableWithinAt

/-- g''(t) ≥ 0 for t ≥ 0. Follows from g''(0) = 0 and g''' ≥ 0. -/
private lemma gAux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux'' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_gAux''
  · intro x hx
    rw [(hasDerivAt_gAux'' x).deriv]
    exact gAux'''_nonneg hx
  · exact gAux''_zero
  · exact ht

private lemma gAux''_pos {t : ℝ} (ht : 0 < t) : 0 < gAux'' t := by
  have hdiff : Differentiable ℝ gAux'' := fun x => (hasDerivAt_gAux'' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv gAux'' x := fun x hx => by
    simpa [(hasDerivAt_gAux'' x).deriv] using gAux'''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [gAux''_zero] using this

/-- g'(t) ≥ 0 for t ≥ 0. Follows from g'(0) = 0 and g'' ≥ 0. -/
private lemma gAux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_gAux'
  · intro x hx
    rw [(hasDerivAt_gAux' x).deriv]
    exact gAux''_nonneg hx
  · exact gAux'_zero
  · exact ht

private lemma gAux'_pos {t : ℝ} (ht : 0 < t) : 0 < gAux' t := by
  have hdiff : Differentiable ℝ gAux' := fun x => (hasDerivAt_gAux' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv gAux' x := fun x hx => by
    simpa [(hasDerivAt_gAux' x).deriv] using gAux''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [gAux'_zero] using this

/-- g(t) ≥ 0 for t ≥ 0. This is the key inequality for proving Ktilde t ≤ 1/12.
Follows from g(0) = 0 and g' ≥ 0. -/
private lemma gAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_gAux
  · intro x hx
    rw [(hasDerivAt_gAux x).deriv]
    exact gAux'_nonneg hx
  · exact gAux_zero
  · exact ht

private lemma gAux_pos {t : ℝ} (ht : 0 < t) : 0 < gAux t := by
  have hdiff : Differentiable ℝ gAux := fun x => (hasDerivAt_gAux x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv gAux x := fun x hx => by
    simpa [(hasDerivAt_gAux x).deriv] using gAux'_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [gAux_zero] using this

/-- The Taylor expansion shows K(t) = t/12 - t³/720 + O(t⁵), so K(t)/t → 1/12 as t → 0⁺.
Since K(t) < t/12 for t > 0 (the higher order terms are negative), we have K(t)/t < 1/12.

The proof uses the algebraic identity K(t) = f(t)/(2t(e^t-1)) and bounds on f. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1/12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]
  · have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos hpos
    have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
    have hf_nonneg : 0 ≤ f t := f_nonneg (le_of_lt hpos)
    calc Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos hpos
      _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
          rw [← K_pos hpos, K_eq_alt' hpos]
      _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
          unfold f
          field_simp
      _ ≤ 1 / 12 := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1))
            (by norm_num : (0 : ℝ) < 12)]
          have h_nonneg : 0 ≤ gAux t := gAux_nonneg (le_of_lt hpos)
          have hgoal : 0 ≤ 2 * gAux t := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_nonneg
          unfold gAux at hgoal
          unfold f
          linarith [hgoal, Real.exp_pos t, sq_nonneg t]

theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  calc
    Ktilde t
        = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
            have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
            calc
              Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
              _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
                    rw [← K_pos ht, K_eq_alt' ht]
              _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
                    unfold f
                    field_simp
    _ < 1 / 12 := by
          have hdenom : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := by positivity
          have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
          rw [div_lt_div_iff₀ hdenom h12]
          have hpos_g : 0 < gAux t := gAux_pos ht
          have hpos : 0 < 2 * gAux t := mul_pos (by norm_num) hpos_g
          unfold gAux at hpos
          unfold f
          linarith [hpos, Real.exp_pos t, sq_nonneg t]

/-! ## Section 4b: Robbins-type lower bound for `Ktilde` -/

/-!
Robbins' sharpened factorial lower bound is equivalent (via Binet's integral) to a pointwise
lower bound on the Binet kernel:

`(1/12) * exp(-t/12) ≤ Ktilde t` for all `t > 0`.

We prove this by reducing it to positivity of an explicit auxiliary function and then using a
derivative-chain argument (similar to the proof of `Ktilde_le`).
-/

private noncomputable def robbinsAux (t : ℝ) : ℝ :=
  12 * Real.exp (t * (13 / 12 : ℝ)) * (t - 2)
    + 12 * Real.exp (t * (1 / 12 : ℝ)) * (t + 2)
    - 2 * t ^ 2 * Real.exp t + 2 * t ^ 2

private noncomputable def robbinsAux' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)
    + Real.exp (t * (1 / 12 : ℝ)) * (t + 14)
    - 2 * Real.exp t * (t * (t + 2)) + 4 * t

private noncomputable def robbinsAux'' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)
    - 2 * Real.exp t * (t ^ 2 + 4 * t + 2) + 4

private noncomputable def robbinsAux''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)
    - 2 * Real.exp t * (t ^ 2 + 6 * t + 6)

private noncomputable def robbinsAux'''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)
    - 2 * Real.exp t * (t ^ 2 + 8 * t + 12)

private lemma robbinsAux_zero : robbinsAux 0 = 0 := by
  simp [robbinsAux]

private lemma robbinsAux'_zero : robbinsAux' 0 = 0 := by
  simp [robbinsAux']

private lemma robbinsAux''_zero : robbinsAux'' 0 = 0 := by
  simp [robbinsAux'']
  norm_num

private lemma robbinsAux'''_zero : robbinsAux''' 0 = 0 := by
  simp [robbinsAux''']; norm_num

private lemma hasDerivAt_robbinsAux (t : ℝ) : HasDerivAt robbinsAux (robbinsAux' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
        (Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
          (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ) * (t - 2) +
            Real.exp (t * (13 / 12 : ℝ)) * 1) t :=
      (hexp13.mul hpoly)
    have h := hmul.const_mul (12 : ℝ)
    convert h using 1 <;> ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
        (Real.exp (t * (1 / 12 : ℝ)) * (t + 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
          (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ) * (t + 2) +
            Real.exp (t * (1 / 12 : ℝ)) * 1) t :=
      (hexp1.mul hpoly)
    have h := hmul.const_mul (12 : ℝ)
    convert h using 1 <;> ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * x ^ 2 * Real.exp x)
        (-2 * (Real.exp t * (t * (t + 2)))) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hmul : HasDerivAt (fun x : ℝ => x ^ 2 * Real.exp x)
        ((2 : ℝ) * t * Real.exp t + t ^ 2 * Real.exp t) t := hpow.mul hexp
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1 <;> ring_nf
  have hD :
      HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * t) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h := hpow.const_mul (2 : ℝ)
    convert h using 1; ring_nf
  have h := ((hA.add hB).add (hC.add hD))
  unfold robbinsAux robbinsAux'
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux' (t : ℝ) : HasDerivAt robbinsAux' (robbinsAux'' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (13 * x - 14))
        (Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => 13 * x - 14) 13 t := by
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).const_mul (13 : ℝ)).sub_const 14
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 14))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 14) 1 t := (hasDerivAt_id t).add_const 14
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x * (x + 2)))
        (-2 * Real.exp t * (t ^ 2 + 4 * t + 2)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x * (x + 2)) (t + (t + 2)) t := by
      have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
      have := h1.mul h2
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h := ((hA.add hB).add (hC.add hD))
  unfold robbinsAux' robbinsAux''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux'' (t : ℝ) : HasDerivAt robbinsAux'' (robbinsAux''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((169 * x - 26) / 12))
        (Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((169 * x - 26) / 12)) (169 / 12) t := by
      have : HasDerivAt (fun x : ℝ => (169 * x - 26)) 169 t := by
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (169 : ℝ)).sub_const 26
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 12 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 26) / 12))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 26) / 12)) (1 / 12) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 26).const_mul (1 / 12 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 4 * x + 2))
        (-2 * Real.exp t * (t ^ 2 + 6 * t + 6)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 4 * x + 2) (2 * t + 4) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
      have := (h1.add (h2.add h3))
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun _x : ℝ => (4 : ℝ)) 0 t := hasDerivAt_const t 4
  have h := ((hA.add hB).add hC).add hD
  unfold robbinsAux'' robbinsAux'''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

private lemma hasDerivAt_robbinsAux''' (t : ℝ) : HasDerivAt robbinsAux''' (robbinsAux'''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((2197 * x + 1690) / 144))
        (Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((2197 * x + 1690) / 144)) (2197 / 144) t := by
      have : HasDerivAt (fun x : ℝ => (2197 * x + 1690)) 2197 t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (2197 : ℝ)).add_const 1690
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 144 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 38) / 144))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 38) / 144)) (1 / 144) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 38).const_mul (1 / 144 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 6 * x + 6))
        (-2 * Real.exp t * (t ^ 2 + 8 * t + 12)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 6 * x + 6) (2 * t + 6) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 6 * x) 6 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (6 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (6 : ℝ)) 0 t := hasDerivAt_const t 6
      have := h1.add (h2.add h3)
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have h := (hA.add hB).add hC
  unfold robbinsAux''' robbinsAux''''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

private lemma differentiableOn_robbinsAux : DifferentiableOn ℝ robbinsAux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux' : DifferentiableOn ℝ robbinsAux' (Set.Ici 0) :=
  fun x _ =>
  (hasDerivAt_robbinsAux' x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux'' : DifferentiableOn ℝ robbinsAux'' (Set.Ici 0) :=
  fun x _ =>
  (hasDerivAt_robbinsAux'' x).differentiableAt.differentiableWithinAt

private lemma differentiableOn_robbinsAux''' : DifferentiableOn ℝ robbinsAux''' (Set.Ici 0) :=
  fun x _ =>
  (hasDerivAt_robbinsAux''' x).differentiableAt.differentiableWithinAt

.integrable.bdd_mul h_meas h_bdd_ae

end BinetKernel
