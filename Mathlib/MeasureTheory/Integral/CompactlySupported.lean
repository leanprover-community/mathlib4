/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Integrating compactly supported continuous functions

This file contains definitions and lemmas related to integrals of compactly supported continuous
functions.
-/

open scoped ENNReal NNReal
open CompactlySupported MeasureTheory

variable {X : Type*}

namespace CompactlySupportedContinuousMap
variable [TopologicalSpace X] [MeasurableSpace X]

lemma integrable {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

/-- Integral as a positive linear functional on `C_c(X, ℝ)`. -/
@[simps!]
noncomputable def integralPositiveLinearMap (μ : Measure X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := ∫ x, f x ∂μ,
      map_add' f g := integral_add' f.integrable g.integrable
      map_smul' c f := integral_smul c f }
    fun _ ↦ integral_nonneg

/-- Integration as a positive linear functional on `C_c(X, ℝ≥0)`. -/
-- Note: the default generated `simps` lemma uses `Subtype.val` instead of `NNReal.toReal`.
@[simps! apply]
noncomputable def integralLinearMap (μ : Measure X) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
  CompactlySupportedContinuousMap.toNNRealLinear (integralPositiveLinearMap μ)

end CompactlySupportedContinuousMap
