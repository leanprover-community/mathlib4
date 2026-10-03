/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Conformal

/-!
# Wirtinger derivatives

For a map `f : ℂ → ℂ` the **Wirtinger derivatives** are the two complex combinations of the
directional real derivatives `(fderiv ℝ f z) 1` and `(fderiv ℝ f z) I`:

* `Complex.wirtingerDeriv f z = (1 / 2) * ((fderiv ℝ f z) 1 - I * (fderiv ℝ f z) I)`
  (the holomorphic derivative `∂f/∂z`),
* `Complex.wirtingerDerivBar f z = (1 / 2) * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)`
  (the antiholomorphic derivative `∂f/∂(conj z)`).

They are defined directly from the real Fréchet derivative `fderiv ℝ`, so they are total: at a
point where `f` is not real-differentiable both return the junk value `0`.

## Main results

* `Complex.differentiableAt_complex_iff_wirtingerDerivBar_eq_zero`: a real-differentiable `f` is
  complex-differentiable at `z` iff `wirtingerDerivBar f z = 0`, which is the Cauchy-Riemann
  equation `(fderiv ℝ f z) I = I • (fderiv ℝ f z) 1`. On an open set,
  `Complex.differentiableOn_complex_iff_wirtingerDerivBar_eq_zero`.
* `DifferentiableAt.wirtingerDeriv_eq_deriv`: where `f` is holomorphic the holomorphic Wirtinger
  derivative agrees with the ordinary complex derivative.
* `Complex.wirtingerDeriv_comp`, `Complex.wirtingerDerivBar_comp`: the Wirtinger chain rules,
  e.g. `wirtingerDeriv (g ∘ f) z = wirtingerDeriv g (f z) * wirtingerDeriv f z +
  wirtingerDerivBar g (f z) * conj (wirtingerDerivBar f z)`.
* `Complex.wirtingerDeriv_fun_mul`, `Complex.wirtingerDerivBar_fun_mul`: the Leibniz product
  rules.
* `Complex.wirtingerDeriv_conj`, `Complex.wirtingerDerivBar_conj`: conjugation swaps the two
  derivatives.

These identities are the calculus in which the Beltrami equation
`wirtingerDerivBar f = μ * wirtingerDeriv f` and the Cauchy and Beurling transforms are written.

## Tags

Wirtinger derivative, Cauchy-Riemann equation, antiholomorphic, Beltrami equation
-/

@[expose] public section

open scoped ComplexConjugate

namespace Complex

variable {f g : ℂ → ℂ} {z : ℂ} {U : Set ℂ}

/-- The holomorphic Wirtinger derivative `∂f/∂z`, built from the real Fréchet derivative of `f`
in the directions `1` and `I`. -/
noncomputable def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 - I * (fderiv ℝ f z) I)

/-- The antiholomorphic Wirtinger derivative `∂f/∂(conj z)`, built from the real Fréchet
derivative of `f` in the directions `1` and `I`. -/
noncomputable def wirtingerDerivBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)

/-- The Wirtinger decomposition of a real-linear map: every `L : ℂ →L[ℝ] ℂ` acts as
`w ↦ a * w + b * conj w`, where `a = (1 / 2) * (L 1 - I * L I)` and
`b = (1 / 2) * (L 1 + I * L I)` are its Wirtinger coefficients. -/
theorem _root_.ContinuousLinearMap.apply_eq_mul_add_mul_conj (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (1 / 2 : ℂ) * (L 1 - I * L I) * w + (1 / 2 : ℂ) * (L 1 + I * L I) * conj w := by
  have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L I := by
    conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by
      rw [real_smul, real_smul, mul_one, re_add_im]]
    rw [map_add, map_smul, map_smul, real_smul, real_smul]
  have hcw : conj w = (↑w.re : ℂ) - ↑w.im * I := by
    conv_lhs => rw [← re_add_im w]
    simp only [map_add, map_mul, conj_I, conj_ofReal]
    ring
  have hw : w = (↑w.re : ℂ) + ↑w.im * I := (re_add_im w).symm
  rw [hLw, hcw]
  set a : ℂ := (↑w.re : ℂ)
  set b : ℂ := (↑w.im : ℂ)
  rw [hw]
  linear_combination (b * L I) * I_mul_I

/-- The vanishing of the antiholomorphic Wirtinger derivative is exactly the Cauchy-Riemann
equation in the form `(fderiv ℝ f z) I = I • (fderiv ℝ f z) 1`. -/
theorem wirtingerDerivBar_eq_zero_iff_fderiv :
    wirtingerDerivBar f z = 0 ↔ (fderiv ℝ f z) I = I • (fderiv ℝ f z) 1 := by
  rw [wirtingerDerivBar, smul_eq_mul]
  set D1 := (fderiv ℝ f z) 1
  set DI := (fderiv ℝ f z) I
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · linear_combination (-I) * h + DI * I_mul_I
  · intro h
    right
    rw [h]
    linear_combination I_mul_I * D1

/-- The Wirtinger derivative of a constant function vanishes. -/
@[simp]
theorem wirtingerDeriv_const (z c : ℂ) : wirtingerDeriv (fun _ ↦ c) z = 0 := by
  simp [wirtingerDeriv]

/-- The antiholomorphic Wirtinger derivative of a constant function vanishes. -/
@[simp]
theorem wirtingerDerivBar_const (z c : ℂ) : wirtingerDerivBar (fun _ ↦ c) z = 0 := by
  simp [wirtingerDerivBar]

/-- The holomorphic Wirtinger derivative of the identity is `1`. -/
@[simp]
theorem wirtingerDeriv_fun_id (z : ℂ) : wirtingerDeriv (fun w ↦ w) z = 1 := by
  simp only [wirtingerDeriv, fderiv_fun_id, ContinuousLinearMap.coe_id', id]
  linear_combination (-1 / 2 : ℂ) * I_mul_I

/-- The antiholomorphic Wirtinger derivative of the identity vanishes. -/
@[simp]
theorem wirtingerDerivBar_fun_id (z : ℂ) : wirtingerDerivBar (fun w ↦ w) z = 0 := by
  simp only [wirtingerDerivBar, fderiv_fun_id, ContinuousLinearMap.coe_id', id]
  linear_combination (1 / 2 : ℂ) * I_mul_I

/-- `wirtingerDeriv` is additive on real-differentiable functions. -/
theorem wirtingerDeriv_fun_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (fun w ↦ f w + g w) z = wirtingerDeriv f z + wirtingerDeriv g z := by
  simp only [wirtingerDeriv, fderiv_fun_add hf hg, add_apply]
  ring

/-- `wirtingerDerivBar` is additive on real-differentiable functions. -/
theorem wirtingerDerivBar_fun_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (fun w ↦ f w + g w) z = wirtingerDerivBar f z + wirtingerDerivBar g z := by
  simp only [wirtingerDerivBar, fderiv_fun_add hf hg, add_apply]
  ring

/-- **Holomorphic characterization, pointwise.** A real-differentiable function is
complex-differentiable at `z` iff its antiholomorphic Wirtinger derivative vanishes there. -/
theorem differentiableAt_complex_iff_wirtingerDerivBar_eq_zero (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ wirtingerDerivBar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, and_iff_right hf,
    ← wirtingerDerivBar_eq_zero_iff_fderiv]

/-- **Holomorphic characterization.** On an open set a real-differentiable function is
holomorphic iff its antiholomorphic Wirtinger derivative vanishes identically. -/
theorem differentiableOn_complex_iff_wirtingerDerivBar_eq_zero (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) :
    DifferentiableOn ℂ f U ↔ ∀ z ∈ U, wirtingerDerivBar f z = 0 := by
  constructor
  · intro hd z hz
    have hfz : DifferentiableAt ℂ f z := (hd z hz).differentiableAt (hU.mem_nhds hz)
    exact (differentiableAt_complex_iff_wirtingerDerivBar_eq_zero
      (differentiableAt_complex_iff_differentiableAt_real.mp hfz).1).mp hfz
  · intro h z hz
    have hfr : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (hU.mem_nhds hz)
    exact ((differentiableAt_complex_iff_wirtingerDerivBar_eq_zero hfr).mpr
      (h z hz)).differentiableWithinAt

/-- A complex-differentiable function has vanishing antiholomorphic Wirtinger derivative. -/
theorem _root_.DifferentiableAt.wirtingerDerivBar_eq_zero (hf : DifferentiableAt ℂ f z) :
    wirtingerDerivBar f z = 0 :=
  (differentiableAt_complex_iff_wirtingerDerivBar_eq_zero
    (differentiableAt_complex_iff_differentiableAt_real.mp hf).1).mp hf

/-- Where `f` is holomorphic the holomorphic Wirtinger derivative is the ordinary complex
derivative. -/
theorem _root_.DifferentiableAt.wirtingerDeriv_eq_deriv (hf : DifferentiableAt ℂ f z) :
    wirtingerDeriv f z = deriv f z := by
  obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hf
  rw [complexOfReal_deriv hr hCR, wirtingerDeriv, hCR, smul_eq_mul]
  linear_combination (-1 / 2 : ℂ) * (fderiv ℝ f z) 1 * I_mul_I

private theorem fderiv_conj_apply (f : ℂ → ℂ) (z v : ℂ) :
    (fderiv ℝ (fun w ↦ conj (f w)) z) v = conj ((fderiv ℝ f z) v) := by
  have heq : (fun w ↦ conj (f w)) = ⇑conjCLE ∘ f := by
    funext w
    simp [Function.comp]
  rw [heq, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply]

/-- Conjugation swaps the Wirtinger derivatives:
`wirtingerDeriv (fun w ↦ conj (f w)) z = conj (wirtingerDerivBar f z)`. -/
theorem wirtingerDeriv_conj (f : ℂ → ℂ) (z : ℂ) :
    wirtingerDeriv (fun w ↦ conj (f w)) z = conj (wirtingerDerivBar f z) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  simp only [wirtingerDeriv, wirtingerDerivBar, fderiv_conj_apply, map_mul, map_add, conj_I,
    hhalf]
  ring

/-- Conjugation swaps the Wirtinger derivatives:
`wirtingerDerivBar (fun w ↦ conj (f w)) z = conj (wirtingerDeriv f z)`. -/
theorem wirtingerDerivBar_conj (f : ℂ → ℂ) (z : ℂ) :
    wirtingerDerivBar (fun w ↦ conj (f w)) z = conj (wirtingerDeriv f z) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  simp only [wirtingerDerivBar, wirtingerDeriv, fderiv_conj_apply, map_mul, map_sub, conj_I,
    hhalf]
  ring

/-- Leibniz product rule for `wirtingerDeriv`. -/
theorem wirtingerDeriv_fun_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (fun w ↦ f w * g w) z =
      f z * wirtingerDeriv g z + g z * wirtingerDeriv f z := by
  have key : fderiv ℝ (fun w ↦ f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [wirtingerDeriv, key, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Leibniz product rule for `wirtingerDerivBar`. -/
theorem wirtingerDerivBar_fun_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (fun w ↦ f w * g w) z =
      f z * wirtingerDerivBar g z + g z * wirtingerDerivBar f z := by
  have key : fderiv ℝ (fun w ↦ f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [wirtingerDerivBar, key, add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Wirtinger chain rule** for the holomorphic derivative:
`wirtingerDeriv (g ∘ f) z = wirtingerDeriv g (f z) * wirtingerDeriv f z +
wirtingerDerivBar g (f z) * conj (wirtingerDerivBar f z)`. -/
theorem wirtingerDeriv_comp (hg : DifferentiableAt ℝ g (f z)) (hf : DifferentiableAt ℝ f z) :
    wirtingerDeriv (g ∘ f) z =
      wirtingerDeriv g (f z) * wirtingerDeriv f z +
        wirtingerDerivBar g (f z) * conj (wirtingerDerivBar f z) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have hcomp : fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  simp only [wirtingerDeriv, wirtingerDerivBar, hcomp, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.apply_eq_mul_add_mul_conj (fderiv ℝ g (f z)) ((fderiv ℝ f z) 1),
    ContinuousLinearMap.apply_eq_mul_add_mul_conj (fderiv ℝ g (f z)) ((fderiv ℝ f z) I)]
  simp only [map_add, map_mul, conj_I, hhalf]
  ring

/-- **Wirtinger chain rule** for the antiholomorphic derivative:
`wirtingerDerivBar (g ∘ f) z = wirtingerDeriv g (f z) * wirtingerDerivBar f z +
wirtingerDerivBar g (f z) * conj (wirtingerDeriv f z)`. -/
theorem wirtingerDerivBar_comp (hg : DifferentiableAt ℝ g (f z)) (hf : DifferentiableAt ℝ f z) :
    wirtingerDerivBar (g ∘ f) z =
      wirtingerDeriv g (f z) * wirtingerDerivBar f z +
        wirtingerDerivBar g (f z) * conj (wirtingerDeriv f z) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have hcomp : fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  simp only [wirtingerDeriv, wirtingerDerivBar, hcomp, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.apply_eq_mul_add_mul_conj (fderiv ℝ g (f z)) ((fderiv ℝ f z) 1),
    ContinuousLinearMap.apply_eq_mul_add_mul_conj (fderiv ℝ g (f z)) ((fderiv ℝ f z) I)]
  simp only [map_sub, map_mul, conj_I, hhalf]
  ring

end Complex
