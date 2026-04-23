/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.T5

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

@[expose] public section

variable {M : Type*} [SeminormedCommGroup M]

variable (M) in
/-- The null subgroup with respect to the norm. -/
@[to_additive /-- The additive null subgroup with respect to the norm. -/]
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
