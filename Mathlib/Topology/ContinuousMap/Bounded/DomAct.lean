/-
Copyright (c) 2026 Ezequiel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.Topology.Algebra.Constructions.DomMulAct
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.DomAct

/-!
# Action of `Mᵈᵐᵃ` on `α →ᵇ β`

If `M` acts continuously on `α`, then `Mᵈᵐᵃ` acts on bounded continuous functions `α →ᵇ β` by
`(c • f) a = f (mk.symm c • a)`.

## Tags

group action, bounded continuous map, domain action
-/

public section

open BoundedContinuousFunction

namespace DomMulAct

variable {M α β : Type*}
variable [TopologicalSpace α] [PseudoMetricSpace β]

section SMul

variable [SMul M α] [TopologicalSpace M] [ContinuousConstSMul M α]

/-- The action of `Mᵈᵐᵃ` on `α →ᵇ β` induced by the action on `α`. -/
noncomputable def smulBoundedContinuousFunction (c : Mᵈᵐᵃ) (f : α →ᵇ β) : α →ᵇ β :=
  mkOfBound (c • f.toContinuousMap) (Classical.choose f.bounded)
    fun x y => Classical.choose_spec f.bounded (mk.symm c • x) (mk.symm c • y)

noncomputable instance instSMulBoundedContinuousFunction : SMul Mᵈᵐᵃ (α →ᵇ β) where
  smul := smulBoundedContinuousFunction

omit [TopologicalSpace M] in
theorem smulBoundedContinuousFunction_apply (c : Mᵈᵐᵃ) (f : α →ᵇ β) (a : α) :
    smulBoundedContinuousFunction c f a = f (mk.symm c • a) := by
  simp only [smulBoundedContinuousFunction, mkOfBound_coe, smul_continuousMap_apply,
    coe_toContinuousMap]

omit [TopologicalSpace M] in
theorem smul_boundedContinuousFunction_apply (c : Mᵈᵐᵃ) (f : α →ᵇ β) (a : α) :
    (c • f) a = f (mk.symm c • a) :=
  smulBoundedContinuousFunction_apply c f a

omit [TopologicalSpace M] in
@[simp]
theorem coe_smul_boundedContinuousFunction (c : Mᵈᵐᵃ) (f : α →ᵇ β) :
    ⇑(c • f) = c • ⇑f := by
  funext a
  rw [smul_boundedContinuousFunction_apply, DomMulAct.smul_apply]

omit [TopologicalSpace M] in
@[simp]
theorem mk_smul_boundedContinuousFunction_apply (c : M) (f : α →ᵇ β) (a : α) :
    (mk c • f) a = f (c • a) := by
  simp [smul_boundedContinuousFunction_apply]

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [TopologicalSpace M] [ContinuousConstSMul M α]

noncomputable instance instMulActionBoundedContinuousFunction : MulAction Mᵈᵐᵃ (α →ᵇ β) where
  smul := (· • ·)
  one_smul f := by ext; simp [smul_boundedContinuousFunction_apply]
  mul_smul x y f := by ext; simp [smul_boundedContinuousFunction_apply, mul_smul]

end MulAction

end DomMulAct
