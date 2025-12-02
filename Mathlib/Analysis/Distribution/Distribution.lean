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
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕂 F']
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

section mapCLM

def mapCLM (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  .postcomp (𝓓^{n}(Ω, ℝ)) A

@[simp]
lemma mapCLM_apply {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

-- TODO: naming...
noncomputable def mapCLE (A : F ≃L[ℝ] F') : 𝓓'^{n}(Ω, F) ≃L[ℝ] 𝓓'^{n}(Ω, F') :=
  (ContinuousLinearEquiv.refl ℝ 𝓓^{n}(Ω, ℝ)).arrowCongr A

@[simp]
lemma mapCLE_apply {A : F ≃L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLE A T f = A (T f) := rfl

@[simp]
lemma mapCLE_symm {A : F ≃L[ℝ] F'} :
    (mapCLE A : 𝓓'^{n}(Ω, F) ≃L[ℝ] 𝓓'^{n}(Ω, F')).symm = mapCLE A.symm := rfl

end mapCLM

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

@[simp]
lemma ofFunWithOrder_zero {μ : Measure E} : ofFunWithOrder Ω n (0 : E → F) μ = 0 := by
  ext φ
  simp [ofFunWithOrder, TestFunction.integralAgainstBilinCLM, TestFunction.integralAgainstBilinLM]

@[simp]
lemma ofFun_zero {μ : Measure E} : ofFun Ω (0 : E → F) μ = 0 := by
  ext φ
  simp [ofFun]

-- TODO: find a better name!
lemma integrable_smul {f : E → F} {μ : Measure E} (φ : 𝓓(Ω, ℝ)) (hf : LocallyIntegrableOn f Ω μ) :
    Integrable (fun x ↦ φ x • f x) μ := by
  sorry -- φ has support inside Ω, and f is integrable on Ω

@[simp]
lemma ofFun_add {f g : E → F} {μ : Measure E}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ) :
    ofFun Ω (f + g) μ = ofFun Ω f μ + ofFun Ω g μ := by
  ext φ
  simp only [ContinuousLinearMap.add_apply]
  rw [ofFun_apply hf, ofFun_apply hg, ofFun_apply (hf.add hg),
    ← integral_add (integrable_smul φ hf) (integrable_smul φ hg)]
  congr with x
  simp

lemma ofFunWithOrder_of_not_locallyIntegrable {f : E → F} {μ : Measure E}
    (hf : ¬LocallyIntegrableOn f Ω μ) : ofFunWithOrder Ω n f μ = 0 := by
  ext φ
  simp [ofFunWithOrder, TestFunction.integralAgainstBilinCLM,
    TestFunction.integralAgainstBilinLM, hf]

lemma ofFun_of_not_locallyIntegrable {f : E → F} {μ : Measure E} (hf : ¬LocallyIntegrableOn f Ω μ) :
    ofFun Ω f μ = 0 := by
  ext φ
  simp [ofFun, ofFunWithOrder_of_not_locallyIntegrable hf]

@[simp]
lemma ofFun_smul {f : E → F} {μ : Measure E} (c : ℝ) : ofFun Ω (c • f) μ = c • ofFun Ω f μ := by
  by_cases! hc : c = 0
  · simp [hc]
  by_cases hf: LocallyIntegrableOn f Ω μ; swap
  · have : ¬ LocallyIntegrableOn (c • f) Ω μ := sorry -- using hc and hf
    simp [ofFun_of_not_locallyIntegrable this, ofFun_of_not_locallyIntegrable hf]
  ext φ
  rw [ofFun_apply (hf.smul c)]
  simp only [Pi.smul_apply, ContinuousLinearMap.coe_smul']
  rw [ofFun_apply hf, ← integral_smul c]
  congr with x
  module

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

-- Everything below is quite experimental, although mathematically correct

section fderiv

variable [FiniteDimensional ℝ E]

-- NOTE: these definitions will change (but not their type).
-- Essentially, using the fact that `E` is finite dimensional, you can put the `v : E`
-- argument wherever you want and keep continuity

-- TODO: where to put the minus ? Doesn't matter mathematically of course
noncomputable def fderivCLM :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F) where
  toFun T :=
  { toFun f :=
    { toFun v := lineDerivCLM v T f
      map_add' := sorry
      map_smul' := sorry
      cont := have : FiniteDimensional ℝ E := inferInstance; sorry }
    map_add' := sorry
    map_smul' := sorry
    cont := sorry }
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

end fderiv

section iteratedFDeriv

variable [FiniteDimensional ℝ E]

noncomputable def iteratedFDerivCLM (i : ℕ) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E [×i]→L[ℝ] F) :=
  Nat.recOn i
    (mapCLM (continuousMultilinearCurryFin0 ℝ E F).symm)
    fun j rec ↦
      letI C : (E →L[ℝ] E [×j]→L[ℝ] F) →L[ℝ] (E [×(j+1)]→L[ℝ] F) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun (_ : Fin j.succ) ↦ E) F).symm
      (mapCLM C) ∘L fderivCLM ∘L rec

-- TODO: write lemmas for this...

end iteratedFDeriv

end Distribution
