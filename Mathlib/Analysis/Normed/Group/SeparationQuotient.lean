/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, the quotient `SeparationQuotient M` by the null subgroup is
defined as a `NormedAddCommGroup` instance in `Mathlib.Analysis.Normed.Group.Uniform`. Here we
define the null space as a subgroup.

## Main definitions

We use `M` to denote seminormed groups.
All the following definitions are in the `SeparationQuotient` namespace. Hence we can access
`SeparationQuotient.normedMk` as `normedMk`.

* `nullSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

If `E` is a vector space over `𝕜` with an appropriate continuous action, we also define the null
subspace as a submodule of `E`.

* `nullSubmodule` : the subspace of elements `x` with `‖x‖ = 0`.

## Implementation details

For any `SeminormedAddCommGroup M`, we define a norm on `SeparationQuotient M` by
`‖x‖ = ‖mk x‖` using the lift.

-/


noncomputable section

open SeparationQuotient Set

variable {M : Type*} [SeminormedAddCommGroup M]

namespace SeparationQuotient

variable (M) in
/-- The null subgroup with respect to the norm. -/
def nullSubgroup : AddSubgroup M where
  carrier := {x : M | ‖x‖ = 0}
  add_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_add_le x y).trans_eq ?_
    rw [hx, hy, add_zero]
  zero_mem' := norm_zero
  neg_mem' {x} (hx : ‖x‖ = 0) := by simpa only [mem_setOf_eq, norm_neg] using hx

lemma isClosed_nullSubgroup : IsClosed (nullSubgroup M : Set M) :=
  isClosed_singleton.preimage continuous_norm

@[simp]
lemma mem_nullSubgroup_iff {x : M} : x ∈ nullSubgroup M ↔ ‖x‖ = 0 := Iff.rfl

variable (x : SeparationQuotient M)

variable (z : M)

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSubgroup`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ ‖m‖ = 0 := by
  rw [← norm_mk]
  exact Iff.symm norm_eq_zero

variable (𝕜 E : Type*)
variable [SeminormedAddCommGroup E] [NormedDivisionRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- The null space with respect to the norm. -/
def nullSubmodule : Submodule 𝕜 E where
  __ := nullSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by simp [norm_smul, hx]

@[simp]
lemma mem_nullSubmodule_iff {x : E} : x ∈ nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl

end SeparationQuotient

end
