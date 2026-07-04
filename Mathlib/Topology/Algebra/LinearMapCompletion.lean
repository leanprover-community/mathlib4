/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Completion of continuous (semi-)linear maps:

This file has a declaration that enables a continuous (semi-)linear map between modules to be
lifted to a continuous semilinear map between the completions of those modules.

## Main declarations:

* `ContinuousLinearMap.completion`: promotes a continuous semilinear map
  from `G` to `H` to a continuous semilinear map from `Completion G` to `Completion H`.
-/

@[expose] public section

namespace ContinuousLinearMap

open UniformSpace Completion

section completion

variable {α β : Type*} {R₁ R₂ : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring R₁] [Module R₁ α] [UniformContinuousConstSMul R₁ α] [Semiring R₂] [UniformSpace β]
  [AddCommGroup β] [IsUniformAddGroup β] [Module R₂ β] [UniformContinuousConstSMul R₂ β]
  {σ : R₁ →+* R₂}

/--
Lift a continuous semilinear map to a continuous semilinear map between the
`UniformSpace.Completion`s of the spaces. This is `UniformSpace.Completion.map` bundled as a
continuous linear map when the input is itself a continuous linear map.
-/
noncomputable def completion (f : α →SL[σ] β) : Completion α →SL[σ] Completion β where
  __ := f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.fun_const_smul _)
    | ih x => simp [← Completion.coe_smul]

@[simp]
lemma toAddMonoidHom_completion (f : α →SL[σ] β) :
    f.completion.toAddMonoidHom = f.toAddMonoidHom.completion f.continuous := rfl

lemma coe_completion (f : α →SL[σ] β) :
    f.completion = Completion.map f := rfl

@[simp]
theorem completion_apply_coe (f : α →SL[σ] β) (a : α) :
    f.completion a = f a := by simp [coe_completion, map_coe]

end completion

section fromCompletion

variable {R₁ R₂ E F : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} [UniformSpace E]
    [AddCommGroup E] [Module R₁ E] [UniformContinuousConstSMul R₁ E] [IsUniformAddGroup E]
    [UniformSpace F] [AddCommGroup F] [Module R₂ F] [T2Space F] [ContinuousAdd F] [CompleteSpace F]
    [ContinuousConstSMul R₂ F]

/-- Extension of a linear function to a linear function over the completion. This is the continuous
linear version of `UniformSpace.Completion.extension`. -/
noncomputable def fromCompletion {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) :
    Completion E →SL[σ₁₂] F where
  toFun := Completion.extension f
  map_add' a b := induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop)) <| by
    simp [extension_coe, hf, ← coe_add]
  map_smul' c a := induction_on a
      (isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by fun_prop)) <| by
    simp [← Completion.coe_smul, hf, extension_coe]

lemma coe_fromCompletion {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) :
    fromCompletion hf = Completion.extension f := rfl

@[simp]
lemma fromCompletion_apply {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) (e : Completion E) :
    fromCompletion hf e = Completion.extension f e := rfl

lemma uniformContinuous_fromCompletion {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f) :
    UniformContinuous (fromCompletion hf) :=
  uniformContinuous_def.mpr (uniformContinuous_extension)

lemma fromCompletion_unique {f : E →ₛₗ[σ₁₂] F} (hf : UniformContinuous f)
    {g : Completion E →SL[σ₁₂] F} (hg : UniformContinuous g) (h : ∀ (e : E), f e = g e) :
    fromCompletion hf = g := by
  ext; simp [extension_unique hf hg h]

noncomputable def fromCompletion' [IsUniformAddGroup F] (f : E →SL[σ₁₂] F) :
    Completion E →SL[σ₁₂] F :=
  fromCompletion (uniformContinuous_of_continuousAt_zero f (by exact f.continuous.continuousAt))

end fromCompletion

end ContinuousLinearMap
