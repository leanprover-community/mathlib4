/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Completion of (Semi-)Linear Maps Between AddCommGroups:

This file has a declaration that enables a (semi-)linear map between `AddCommGroup`s to be raised
to a (semi-)linear map between their completions.

## Main declarations:

* `UniformSpace.Completion.mapCLM`: promotes a continuous semilinear map
  from `G` to `H` into a continuous semilinear map
  from `Completion G` to `Completion H`.
-/

@[expose] public section

namespace UniformSpace.Completion

variable {α β : Type*} {R₁ R₂ : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring R₁] [Module R₁ α] [UniformContinuousConstSMul R₁ α] [Semiring R₂] [UniformSpace β]
  [AddCommGroup β] [IsUniformAddGroup β] [Module R₂ β] [UniformContinuousConstSMul R₂ β]
  {σ : R₁ →+* R₂}

/--
Constructs a continuous semilinear map between completions of `AddCommGroup`s from a continuous
semilinear map between the `AddCommGroup`s.
-/
@[simps]
noncomputable def mapCLM (f : α →SL[σ] β) : (Completion α) →SL[σ] (Completion β) where
  __ := f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.const_smul _)
    | ih x => simp [← Completion.coe_smul, AddMonoidHom.completion_coe]
  cont := continuous_map

@[simp]
theorem mapCLM_apply_coe (f : α →SL[σ] β) (a : α) :
    mapCLM f a = f a := by simp [mapCLM, AddMonoidHom.completion_coe]

end UniformSpace.Completion
