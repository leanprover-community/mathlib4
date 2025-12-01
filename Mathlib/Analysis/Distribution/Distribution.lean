/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.LocallyConvex.StrongTopology

/-!
# Distributions
-/

@[expose] public section

open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology ContDiff Distributions

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace 𝕂 F]
  {n k : ℕ∞}

-- TODO: def or abbrev?
variable (Ω F n) in
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →L[ℝ] F

-- TODO: I'm not sure these notations are good
/-- Notation for the space of distributions of order less than `n`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- Notation for the space of distributions. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

noncomputable example : TopologicalSpace 𝓓'(Ω, F) := inferInstance
example : IsTopologicalAddGroup 𝓓'(Ω, F) := inferInstance

-- TODO: generalize `ContinuousLinearMap.continuousSMul`
example : ContinuousSMul ℝ 𝓓'(Ω, F) := inferInstance
example : LocallyConvexSpace ℝ 𝓓'(Ω, F) := inferInstance

namespace Distribution

section ofFun

variable [MeasurableSpace E] [OpensMeasurableSpace E]

variable (Ω n) in
noncomputable def ofFunWithOrder (f : E → F) (μ : Measure E := by volume_tac) :
    𝓓'^{n}(Ω, F) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ f

variable (Ω) in
noncomputable def ofFun (f : E → F) (μ : Measure E := by volume_tac) : 𝓓'(Ω, F) :=
  ofFunWithOrder Ω ⊤ f μ

-- TODO: be more consistent about the naming: which is φ and which is f ?

@[simp]
lemma ofFunWithOrder_apply {f : E → F} {μ : Measure E} (hf : LocallyIntegrableOn f Ω μ)
    {φ : 𝓓^{n}(Ω, ℝ)} :
    ofFunWithOrder Ω n f μ φ = ∫ x, φ x • f x ∂μ := by
  simp [ofFunWithOrder, hf]

@[simp]
lemma ofFun_apply {f : E → F} {μ : Measure E} (hf : LocallyIntegrableOn f Ω μ)
    {φ : 𝓓(Ω, ℝ)} :
    ofFun Ω f μ φ = ∫ x, φ x • f x ∂μ :=
  ofFunWithOrder_apply hf

end ofFun

section lineDeriv

-- TODO: where to put the minus ? Doesn't matter mathematically of course
variable (n k) in
noncomputable def lineDerivWithOrderCLM (v : E) :
    𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{k}(Ω, F) :=
  .precomp F (- TestFunction.lineDerivWithOrderCLM k n v)

@[simp]
lemma lineDerivWithOrderCLM_apply {v : E} {T : 𝓓'^{n}(Ω, F)} {φ : 𝓓^{k}(Ω, ℝ)} :
    lineDerivWithOrderCLM n k v T φ = T (- TestFunction.lineDerivWithOrderCLM k n v φ) :=
  rfl

-- TODO: where to put the minus ? Doesn't matter mathematically of course
noncomputable def lineDerivCLM (v : E) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F) :=
  .precomp F (- TestFunction.lineDerivCLM v)

@[simp]
lemma lineDerivCLM_apply {v : E} {T : 𝓓'(Ω, F)} {φ : 𝓓(Ω, ℝ)} :
    lineDerivCLM v T φ = T (- TestFunction.lineDerivCLM v φ) :=
  rfl

end lineDeriv

end Distribution
