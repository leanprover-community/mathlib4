/-
Copyright (c) 2026 Jan Bernlöhr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Bernlöhr
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral Grönwall inequality

The integral form of **Grönwall's inequality** bounds a function satisfying
`f t ≤ c + ∫ s in a..t, β s * f s` by `c * exp (∫ s in a..t, β s)`.
The coefficient is nonnegative; neither the function nor the constant needs to be nonnegative.

See `Mathlib.Analysis.ODE.Gronwall` for differential inequalities with constant coefficients.
-/

public section

open Set MeasureTheory intervalIntegral Real

/-- **Grönwall's inequality**, integral form with a variable coefficient.
Continuity is required only on the interval, and no sign assumption on `f` or `c` is needed. -/
theorem le_mul_exp_integral_of_le_const_add_integral {f β : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hβ_nonneg : ∀ s ∈ Icc a b, 0 ≤ β s)
    (hbound : ∀ t ∈ Icc a b, f t ≤ c + ∫ s in a..t, β s * f s) :
    ∀ t ∈ Icc a b, f t ≤ c * exp (∫ s in a..t, β s) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hcont {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
      ContinuousOn (fun x ↦ ∫ s in a..x, g s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      continuousOn_primitive_interval' (hg.intervalIntegrable_of_Icc hab) left_mem_uIcc
  have hderiv {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) {x : ℝ}
      (hx : x ∈ Ioo a b) : HasDerivAt (fun y ↦ ∫ s in a..y, g s) (g x) x :=
    integral_hasDerivAt_right
      ((hg.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le)
      ((hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hg.continuousAt (Icc_mem_nhds hx.1 hx.2))
  let F := fun x ↦ c + ∫ s in a..x, β s * f s
  let B := fun x ↦ ∫ s in a..x, β s
  let G := fun x ↦ F x * exp (-B x)
  have hG {x : ℝ} (hx : x ∈ interior (Icc a b)) :
      HasDerivAt G (β x * (f x - F x) * exp (-B x)) x := by
    rw [interior_Icc] at hx
    convert ((hderiv (hβ.mul hf) hx).const_add c).mul (hderiv hβ hx).neg.exp using 1
    dsimp [G, F, B]
    ring
  have hanti : AntitoneOn G (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (f := G) (convex_Icc a b)
      ((continuousOn_const.add (hcont (hβ.mul hf))).mul (hcont hβ).neg.rexp)
      (fun x hx ↦ (hG hx).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hG hx).deriv]
    have hx' : x ∈ Icc a b := interior_subset hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hβ_nonneg x hx') (sub_nonpos.mpr (hbound x hx')))
      (exp_nonneg _)
  have hle : F t * exp (-B t) ≤ c := by
    simpa [G, F, B] using hanti (left_mem_Icc.mpr hab) ht ht.1
  calc
    f t ≤ F t := hbound t ht
    _ ≤ c / exp (-B t) := (le_div_iff₀ (exp_pos _)).mpr hle
    _ = c * exp (∫ s in a..t, β s) := by rw [exp_neg, div_inv_eq_mul]
