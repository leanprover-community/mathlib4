/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Measurability of the line derivative

We prove in `measurable_lineDeriv` that the line derivative of a function (with respect to a
locally compact scalar field) is measurable, provided the function is continuous.

In `measurable_lineDeriv_uncurry`, assuming additionally that the source space is second countable,
we show that `(x, v) ↦ lineDeriv 𝕜 f x v` is also measurable.

An assumption such as continuity is necessary, as otherwise one could alternate in a non-measurable
way between differentiable and non-differentiable functions along the various lines
directed by `v`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open MeasureTheory

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {v : E}

/-!
Measurability of the line derivative `lineDeriv 𝕜 f x v` with respect to a fixed direction `v`.
-/

theorem measurableSet_lineDifferentiableAt (hf : Continuous f) :
    MeasurableSet {x : E | LineDifferentiableAt 𝕜 f x v} := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact measurable_prodMk_right (measurableSet_of_differentiableAt_with_param 𝕜 hg)

theorem measurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) : Measurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact (measurable_deriv_with_param hg).comp measurable_prodMk_right

theorem stronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F] (hf : Continuous f) :
    StronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) := by
  borelize 𝕜
  let g : E → 𝕜 → F := fun x t ↦ f (x + t • v)
  have hg : Continuous g.uncurry := by fun_prop
  exact (stronglyMeasurable_deriv_with_param hg).comp_measurable measurable_prodMk_right

theorem aemeasurable_lineDeriv [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) (μ : Measure E) :
    AEMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (measurable_lineDeriv hf).aemeasurable

theorem aestronglyMeasurable_lineDeriv [SecondCountableTopologyEither E F]
    (hf : Continuous f) (μ : Measure E) :
    AEStronglyMeasurable (fun x ↦ lineDeriv 𝕜 f x v) μ :=
  (stronglyMeasurable_lineDeriv hf).aestronglyMeasurable

/-!
Measurability of the line derivative `lineDeriv 𝕜 f x v` when varying both `x` and `v`. For this,
we need an additional second countability assumption on `E` to make sure that open sets are
measurable in `E × E`.
-/

variable [SecondCountableTopology E]

theorem measurableSet_lineDifferentiableAt_uncurry (hf : Continuous f) :
    MeasurableSet {p : E × E | LineDifferentiableAt 𝕜 f p.1 p.2} := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  have M_meas : MeasurableSet {q : (E × E) × 𝕜 | DifferentiableAt 𝕜 (g q.1) q.2} :=
    measurableSet_of_differentiableAt_with_param 𝕜 this
  exact measurable_prodMk_right M_meas

theorem measurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) : Measurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  exact (measurable_deriv_with_param this).comp measurable_prodMk_right

theorem stronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) :
    StronglyMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) := by
  borelize 𝕜
  let g : (E × E) → 𝕜 → F := fun p t ↦ f (p.1 + t • p.2)
  have : Continuous g.uncurry :=
    hf.comp <| (continuous_fst.comp continuous_fst).add
    <| continuous_snd.smul (continuous_snd.comp continuous_fst)
  exact (stronglyMeasurable_deriv_with_param this).comp_measurable measurable_prodMk_right

theorem aemeasurable_lineDeriv_uncurry [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f) (μ : Measure (E × E)) :
    AEMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) μ :=
  (measurable_lineDeriv_uncurry hf).aemeasurable

theorem aestronglyMeasurable_lineDeriv_uncurry (hf : Continuous f) (μ : Measure (E × E)) :
    AEStronglyMeasurable (fun (p : E × E) ↦ lineDeriv 𝕜 f p.1 p.2) μ :=
  (stronglyMeasurable_lineDeriv_uncurry hf).aestronglyMeasurable
