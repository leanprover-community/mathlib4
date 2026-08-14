/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {f : E → ℝ}

variable [FiniteDimensional ℝ E]

proof_wanted ConvexOn.locallyLipschitzOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn (intrinsicInterior ℝ C) f

proof_wanted ConcaveOn.locallyLipschitzOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn (intrinsicInterior ℝ C) f

proof_wanted ConvexOn.continuousOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
    ContinuousOn f (intrinsicInterior ℝ C)

proof_wanted ConcaveOn.continuousOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
    ContinuousOn f (intrinsicInterior ℝ C)
