/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.MulAction

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, the quotient `SeparationQuotient M` by the null subgroup is
defined as a `NormedAddCommGroup` instance in `Mathlib/Analysis/Normed/Group/Uniform.lean`. Here we
define the null space as a subgroup.

## Main definitions

We use `M` to denote seminormed groups.

* `nullAddSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

If `E` is a vector space over `𝕜` with an appropriate continuous action, we also define the null
subspace as a submodule of `E`.

* `nullSubmodule` : the subspace of elements `x` with `‖x‖ = 0`.

-/

variable {M : Type*} [SeminormedCommGroup M]

variable (M) in
/-- The null subgroup with respect to the norm. -/
@[to_additive "The additive null subgroup with respect to the norm."]
def nullSubgroup : Subgroup M where
  carrier := {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx, hy, add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_setOf_eq, norm_inv'] using hx

@[to_additive]
lemma isClosed_nullSubgroup : IsClosed (nullSubgroup M : Set M) := by
  apply isClosed_singleton.preimage continuous_norm'

@[to_additive (attr := simp)]
lemma mem_nullSubgroup_iff {x : M} : x ∈ nullSubgroup M ↔ ‖x‖ = 0 := Iff.rfl

variable {𝕜 E : Type*}
variable [SeminormedAddCommGroup E] [SeminormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

variable (𝕜 E) in
/-- The null space with respect to the norm. -/
def nullSubmodule : Submodule 𝕜 E where
  __ := nullAddSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_smul_le _ _).trans_eq ?_
    rw [hx, mul_zero]

lemma isClosed_nullSubmodule : IsClosed (nullSubmodule 𝕜 E : Set E) := isClosed_nullAddSubgroup

@[simp]
lemma mem_nullSubmodule_iff {x : E} : x ∈ nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl
