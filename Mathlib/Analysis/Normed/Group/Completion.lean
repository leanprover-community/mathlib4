/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type*)

instance [UniformSpace E] [Norm E] : Norm (Completion E) where
  norm := Completion.extension Norm.norm

@[simp]
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x

instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) where
  dist_eq x y := by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension continuous_sub
    · rw [← Completion.coe_sub, norm_coe, Completion.dist_eq, dist_eq_norm]

@[simp]
theorem nnnorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊ := by
  simp [nnnorm]

@[simp]
lemma enorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ₑ = ‖x‖ₑ := by
  simp [enorm]

end Completion

end UniformSpace
