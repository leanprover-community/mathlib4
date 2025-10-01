/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/

import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported.Basic

/-!
# Integral of compactly supported continuous functions

This file contains definitions and theorems related to integrals of compactly supported continuous
functions.

## Main results

- `integrable`: compactly supported continuous functions are integrable.
-/

open scoped ENNReal NNReal
open CompactlySupported MeasureTheory

variable {X : Type*}

namespace CompactlySupportedContinuousMap

theorem integrable {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

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
