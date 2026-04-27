/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Measurable functions in normed spaces

-/

public section


open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [SeminormedAddCommGroup E] [Module R E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SeminormedAddCommGroup F] [Module R F] [MeasurableSpace F] [BorelSpace F]

@[fun_prop]
protected theorem measurable (L : E →L[R] F) : Measurable L :=
  L.continuous.measurable

@[fun_prop]
theorem measurable_comp (L : E →L[R] F) {φ : α → E} (φ_meas : Measurable φ) :
    Measurable fun a : α => L (φ a) :=
  L.measurable.comp φ_meas

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

instance instMeasurableSpace : MeasurableSpace (E →L[𝕜] F) :=
  borel _

instance instBorelSpace : BorelSpace (E →L[𝕜] F) :=
  ⟨rfl⟩

@[fun_prop]
theorem measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) :
    Measurable fun f : E →L[𝕜] F => f x :=
  (apply 𝕜 F x).continuous.measurable

theorem measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] : Measurable fun (x : E) (f : E →L[𝕜] F) => f x :=
  measurable_pi_lambda _ fun f => f.measurable

theorem measurable_coe [MeasurableSpace F] [BorelSpace F] :
    Measurable fun (f : E →L[𝕜] F) (x : E) => f x :=
  measurable_pi_lambda _ measurable_apply

end ContinuousLinearMap

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[fun_prop]
theorem Measurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : Measurable φ) (v : F) :
    Measurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ

@[fun_prop]
theorem AEMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} {μ : Measure α}
    (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ

end ContinuousLinearMapNontriviallyNormedField

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]
variable [BorelSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [BorelSpace E]

theorem measurable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    (Measurable fun x => f x • c) ↔ Measurable f :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff

theorem aemeasurable_smul_const {f : α → 𝕜} {μ : Measure α} {c : E} (hc : c ≠ 0) :
    AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ :=
  (isClosedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff

end NormedSpace
