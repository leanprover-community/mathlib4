/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

#align_import measure_theory.constructions.borel_space.continuous_linear_map from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

/-!
# Measurable functions in normed spaces

-/


open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace F]
  [BorelSpace F]

@[measurability]
protected theorem measurable (L : E →L[𝕜] F) : Measurable L :=
  L.continuous.measurable
#align continuous_linear_map.measurable ContinuousLinearMap.measurable

theorem measurable_comp (L : E →L[𝕜] F) {φ : α → E} (φ_meas : Measurable φ) :
    Measurable fun a : α => L (φ a) :=
  L.measurable.comp φ_meas
#align continuous_linear_map.measurable_comp ContinuousLinearMap.measurable_comp

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

instance instMeasurableSpace : MeasurableSpace (E →L[𝕜] F) :=
  borel _
#align continuous_linear_map.measurable_space ContinuousLinearMap.instMeasurableSpace

instance instBorelSpace : BorelSpace (E →L[𝕜] F) :=
  ⟨rfl⟩
#align continuous_linear_map.borel_space ContinuousLinearMap.instBorelSpace

@[measurability]
theorem measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) :
    Measurable fun f : E →L[𝕜] F => f x :=
  (apply 𝕜 F x).continuous.measurable
#align continuous_linear_map.measurable_apply ContinuousLinearMap.measurable_apply

@[measurability]
theorem measurable_apply' [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace F]
    [BorelSpace F] : Measurable fun (x : E) (f : E →L[𝕜] F) => f x :=
  measurable_pi_lambda _ fun f => f.measurable
#align continuous_linear_map.measurable_apply' ContinuousLinearMap.measurable_apply'

@[measurability]
theorem measurable_coe [MeasurableSpace F] [BorelSpace F] :
    Measurable fun (f : E →L[𝕜] F) (x : E) => f x :=
  measurable_pi_lambda _ measurable_apply
#align continuous_linear_map.measurable_coe ContinuousLinearMap.measurable_coe

end ContinuousLinearMap

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[measurability]
theorem Measurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : Measurable φ) (v : F) :
    Measurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp hφ
#align measurable.apply_continuous_linear_map Measurable.apply_continuousLinearMap

@[measurability]
theorem AEMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E} {μ : Measure α}
    (hφ : AEMeasurable φ μ) (v : F) : AEMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).measurable.comp_aemeasurable hφ
#align ae_measurable.apply_continuous_linear_map AEMeasurable.apply_continuousLinearMap

end ContinuousLinearMapNontriviallyNormedField

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]
variable [BorelSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E]
  [BorelSpace E]

theorem measurable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    (Measurable fun x => f x • c) ↔ Measurable f :=
  (closedEmbedding_smul_left hc).measurableEmbedding.measurable_comp_iff
#align measurable_smul_const measurable_smul_const

theorem aemeasurable_smul_const {f : α → 𝕜} {μ : Measure α} {c : E} (hc : c ≠ 0) :
    AEMeasurable (fun x => f x • c) μ ↔ AEMeasurable f μ :=
  (closedEmbedding_smul_left hc).measurableEmbedding.aemeasurable_comp_iff
#align ae_measurable_smul_const aemeasurable_smul_const

end NormedSpace
