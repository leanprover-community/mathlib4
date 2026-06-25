/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformField

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/

@[expose] public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*)

instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (Completion E) where
  norm_smul_le := norm_smul_le

section Module

variable {𝕜 E}
variable [Semiring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [UniformContinuousConstSMul 𝕜 E]

/-- Embedding of a normed space to its completion as a linear isometry. -/
def toComplₗᵢ : E →ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E →ₗᵢ[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : E →L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap

@[simp]
theorem coe_toComplL : ⇑(toComplL : E →L[𝕜] Completion E) = ((↑) : E → Completion E) :=
  rfl

@[simp]
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E →L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

end Module

section Algebra

variable (A : Type*)

instance [SeminormedRing A] : NormedRing (Completion A) where
  __ : NormedAddCommGroup (Completion A) := inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul, norm_coe] using norm_mul_le x y

instance [SeminormedCommRing A] : NormedCommRing (Completion A) where
  __ : CommRing (Completion A) := inferInstance
  __ : NormedRing (Completion A) := inferInstance

instance [NormedField 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) where
  norm_smul_le := norm_smul_le

instance [NormedField A] [CompletableTopField A] :
    NormedField (UniformSpace.Completion A) where
  __ : NormedCommRing (Completion A) := inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

end Algebra

section Extension

variable {R₁ R₂ E F : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} [UniformSpace E]
    [AddCommGroup E] [Module R₁ E] [UniformContinuousConstSMul R₁ E] [IsUniformAddGroup E]
    [UniformSpace F] [AddCommGroup F] [Module R₂ F] [T2Space F] [ContinuousAdd F] [CompleteSpace F]
    [ContinuousConstSMul R₂ F]

/-- The continuous linear version of `.extension`. It extends a linear function to a linear function
over the completion. -/
def extensionL {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) : Completion E →SL[σ₁₂] F where
  toFun := Completion.extension f
  map_add' a b := Completion.induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop)) <| by
    simp [extension_coe, hf, ← coe_add]
  map_smul' c a := Completion.induction_on a
      (isClosed_eq (continuous_extension.comp (continuous_const_smul c))
        (continuous_extension.const_smul (σ₁₂ c))) <| by
    simp [extension_coe, hf, ← coe_smul]

@[simp]
lemma extensionL_apply {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) (e : Completion E) :
    extensionL hf e = Completion.extension f e := rfl

lemma uniformContinuous_extensionL {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) :
    UniformContinuous (extensionL hf) :=
  uniformContinuous_def.mpr (UniformSpace.Completion.uniformContinuous_extension)

lemma extensionL_unique {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) {g : Completion E →SL[σ₁₂] F}
    (hg : UniformContinuous g) (h : ∀ (e : E), f e = g e) : extensionL hf = g := by
  ext; simp [UniformSpace.Completion.extension_unique hf hg h]

end Extension

end Completion

end UniformSpace
