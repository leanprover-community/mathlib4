/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variable formulas for integrals in dimension 1
We record in this file versions of the general change of variables formula in integrals for
functions from `R` to `ℝ`. This makes it possible to replace the determinant of the Fréchet
derivative with the one-dimensional derivative.

See also `Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts` for versions of the
change of variables formula in dimension 1 for non-monotone functions, formulated with
the interval integral and with stronger requirements on the integrand.
-/

open MeasureTheory MeasureTheory.Measure Metric Filter Set Module Asymptotics
  TopologicalSpace ContinuousLinearMap

open scoped NNReal ENNReal Topology Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ} {f f' : ℝ → ℝ}
  {g : ℝ → F}

namespace MeasureTheory

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the
Lebesgue integral of a function `g : ℝ → ℝ≥0∞` on `f '' s` coincides with the Lebesgue integral
of `|(f' x)| * g ∘ f` on `s`. -/
theorem lintegral_image_eq_lintegral_abs_deriv_mul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x)  := by
  simpa only [det_one_smulRight] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Integrability in the change of variable formula for differentiable functions (one-variable
version): if a function `f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then a
function `g : ℝ → F` is integrable on `f '' s` if and only if `|(f' x)| • g ∘ f` is integrable on
`s`. -/
theorem integrableOn_image_iff_integrableOn_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : ℝ → F) : IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |f' x| • g (f x)) s := by
  simpa only [det_one_smulRight] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

/-- Change of variable formula for differentiable functions (one-variable version): if a function
`f` is injective and differentiable on a measurable set `s ⊆ ℝ`, then the Bochner integral of a
function `g : ℝ → F` on `f '' s` coincides with the integral of `|(f' x)| • g ∘ f` on `s`. -/
theorem integral_image_eq_integral_abs_deriv_smul
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → F) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  simpa only [det_one_smulRight] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x hx => (hf' x hx).hasFDerivWithinAt) hf g

section WithDensity

lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [hf.withDensity_ofReal_comap_apply_eq_integral_abs_det_fderiv_mul volume hs
    hg hf_int hf']
  simp only [det_one_smulRight]

lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : ∀ᵐ x, x ∈ f '' s → 0 ≤ g x) (hf_int : IntegrableOn g (f '' s))
    {f' : ℝ → ℝ} (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f hg hf_int hf']
  simp only [det_one_smulRight]

lemma _root_.MeasurableEmbedding.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul'
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) :=
  hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul hs
    (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
    (fun x _ => (hf' x).hasDerivWithinAt)

lemma _root_.MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (f : ℝ ≃ᵐ ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    {f' : ℝ → ℝ} (hf' : ∀ x, HasDerivAt f (f' x) x)
    {g : ℝ → ℝ} (hg : 0 ≤ᵐ[volume] g) (hg_int : Integrable g) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * g (f x)) := by
  rw [MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul volume hs
      f (by filter_upwards [hg] with x hx using fun _ ↦ hx) hg_int.integrableOn
      (fun x _ => (hf' x).hasDerivWithinAt)]
  simp only [det_one_smulRight]

end WithDensity

end MeasureTheory
