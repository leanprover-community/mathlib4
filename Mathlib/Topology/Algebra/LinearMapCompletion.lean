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
  from `α` to `β` to a continuous semilinear map from `Completion α` to `Completion β`.
* `ContinuousLinearMap.fromCompletion`: promotes a continuous semilinear map
  from `α` to `β` to a continuous semilinear map from `Completion α` to `β`.
-/

@[expose] public section

namespace ContinuousLinearMap

open UniformSpace Completion

variable {α β : Type*} {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂} [UniformSpace α]
  [AddCommGroup α] [IsUniformAddGroup α] [Module R₁ α] [UniformContinuousConstSMul R₁ α]
  [UniformSpace β] [AddCommGroup β] [Module R₂ β] [UniformContinuousConstSMul R₂ β]

section completion

variable [IsUniformAddGroup β]

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

variable [T2Space β] [ContinuousAdd β] [CompleteSpace β]

/-- Extension of a linear function to a linear function over the completion. This is the continuous
linear version of `UniformSpace.Completion.extension`. -/
noncomputable def fromCompletion {f : α →SL[σ] β} (hf : UniformContinuous f) :
    Completion α →SL[σ] β where
  toFun := Completion.extension f
  map_add' a b := induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop)) <| by
    simp [extension_coe, hf, ← coe_add]
  map_smul' c a := induction_on a
      (isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by fun_prop)) <| by
    simp [← Completion.coe_smul, hf, extension_coe]

lemma coe_fromCompletion {f : α →SL[σ] β} (hf : UniformContinuous f) :
    fromCompletion hf = Completion.extension f := rfl

@[simp]
lemma fromCompletion_apply {f : α →SL[σ] β} (hf : UniformContinuous f) (e : Completion α) :
    fromCompletion hf e = Completion.extension f e := rfl

lemma uniformContinuous_fromCompletion {f : α →SL[σ] β} (hf : UniformContinuous f) :
    UniformContinuous (fromCompletion hf) :=
  uniformContinuous_def.mpr (uniformContinuous_extension)

lemma fromCompletion_unique {f : α →SL[σ] β} (hf : UniformContinuous f)
    {g : Completion α →SL[σ] β} (hg : UniformContinuous g) (h : ∀ (e : α), f e = g e) :
    fromCompletion hf = g := by
  ext; simp [extension_unique hf hg h]

end fromCompletion

end ContinuousLinearMap
