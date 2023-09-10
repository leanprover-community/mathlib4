/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Measurability of the line derivative

We prove in `measurable_lineDeriv` that the line derivative of a function (with respect to a
locally compact scalar field) is measurable, provided the function is continuous.

An assumption such as continuity is necessary, as otherwise one could alternate in a non-measurable
way between differentiable and non-differentiable functions along the various lines
directed by `v`.

TODO: prove (again using the techniques in `Analysis.Calculus.FDeriv.Measurable`) that the line
derivative is measurable as a function of `(x, v)`.
-/

open MeasureTheory
open TopologicalSpace (SecondCountableTopology)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {v : E}

theorem measurableSet_lineDifferentiableAt (hf : Continuous f) :
    MeasurableSet {x : E | LineDifferentiableAt 𝕜 f x v} := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have : Continuous g.uncurry := by apply hf.comp; continuity
  have M_meas : MeasurableSet {p | DifferentiableAt 𝕜 (g p.1) p.2} :=
    measurableSet_of_differentiableAt_with_param 𝕜 this
  exact measurable_prod_mk_right M_meas

theorem measurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) : Measurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by apply hf.comp; continuity
  exact (measurable_deriv_with_param hg).comp measurable_prod_mk_right

theorem stronglyMeasurable_lineDeriv [SecondCountableTopology F] (hf : Continuous f) :
    StronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize F
  exact (measurable_lineDeriv hf).stronglyMeasurable

theorem aemeasurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) (μ : Measure E) :
    AEMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (measurable_lineDeriv hf).aemeasurable

theorem aestronglyMeasurable_lineDeriv [SecondCountableTopology F]
    (hf : Continuous f) (μ : Measure E) :
    AEStronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (stronglyMeasurable_lineDeriv hf).aestronglyMeasurable
