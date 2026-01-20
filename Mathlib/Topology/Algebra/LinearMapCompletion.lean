/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.LinearMap

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

open UniformSpace UniformSpace.Completion

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
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.const_smul _)
    | ih x => simp [← Completion.coe_smul]
  cont := continuous_map

@[simp]
lemma toAddMonoidHom_completion (f : α →SL[σ] β) :
    f.completion.toAddMonoidHom = f.toAddMonoidHom.completion f.continuous := rfl

lemma coe_completion (f : α →SL[σ] β) :
    f.completion = Completion.map f := rfl

@[simp]
theorem completion_apply_coe (f : α →SL[σ] β) (a : α) :
    f.completion a = f a := by simp [coe_completion, map_coe]

end ContinuousLinearMap
