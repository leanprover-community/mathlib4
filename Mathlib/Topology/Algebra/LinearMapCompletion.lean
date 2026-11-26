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

## Main declarations

* `ContinuousLinearMap.completion`: promotes a continuous semilinear map
  from `α` to `β` to a continuous semilinear map from `Completion α` to `Completion β`.
* `ContinuousLinearMap.fromCompletion`: promotes a continuous semilinear map
  from `α` to `β` to a continuous semilinear map from `Completion α` to `β`.
-/

@[expose] public section

variable {α β : Type*} {R S : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring S] [Module S α] [UniformContinuousConstSMul S α] [Semiring R] [UniformSpace β]
  [AddCommGroup β] [IsUniformAddGroup β] [Module R β] [UniformContinuousConstSMul R β]
  {σ : S →+* R}

namespace ContinuousLinearMap

open UniformSpace Completion

section completion

set_option backward.isDefEq.respectTransparency false in
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

variable [T0Space β] [CompleteSpace β]

/-- Extension of a linear function to a linear function over the completion. This is the continuous
linear version of `UniformSpace.Completion.extension`. -/
noncomputable def fromCompletion (f : α →SL[σ] β) :
    Completion α →SL[σ] β where
  __ := f.toAddMonoidHom.extension f.continuous
  map_smul' c a := induction_on a
      (isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by dsimp; fun_prop)) <| by
    simp [← Completion.coe_smul, AddMonoidHom.extension_coe f.toAddMonoidHom f.continuous]

@[simp]
lemma toAddMonoidHom_fromCompletion (f : α →SL[σ] β) :
    f.fromCompletion.toAddMonoidHom = f.toAddMonoidHom.extension f.continuous := rfl

lemma coe_fromCompletion (f : α →SL[σ] β) :
    f.fromCompletion = Completion.extension f := rfl

@[simp]
lemma fromCompletion_apply_coe (f : α →SL[σ] β) (e : α) :
    f.fromCompletion e = f e := by simp [coe_fromCompletion, extension_coe]

lemma fromCompletion_unique (f : α →SL[σ] β) (g : Completion α →SL[σ] β)
    (h : ∀ (e : α), f e = g e) : f.fromCompletion = g := by
  ext; simp [coe_fromCompletion, extension_unique f.uniformContinuous g.uniformContinuous h]

end fromCompletion

end ContinuousLinearMap

namespace UniformSpace.Completion

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def toComplL : α →L[S] Completion α where
  __ := toCompl
  map_smul' := by simp
  cont := continuous_toCompl

@[simp] lemma coe_toComplL : ⇑(toComplL : α →L[S] Completion α) = ((↑) : α → Completion α) := rfl
@[simp] lemma toAddMonoidHom_toComplL : ((toComplL : α →L[S] _) : α →+ _) = toCompl := rfl

end UniformSpace.Completion
