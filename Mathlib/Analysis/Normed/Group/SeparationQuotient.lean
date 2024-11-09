/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib.Analysis.Normed.Group.Uniform`.

## Main definitions

We use `M` to denote seminormed groups.
All the following definitions are in the `NullSubgroup` namespace. Hence we can access
`NullSubgroup.normedMk` as `normedMk`.

* `nullSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

## Implementation details

For any `SeminormedAddCommGroup M`, we define a norm on `SeparationQuotient M` by
`‖x‖ = ‖mk x‖` using the lift.

-/


noncomputable section

open SeparationQuotient Set

variable {M : Type*} [SeminormedAddCommGroup M]

namespace SeparationQuotient

/-- The null subgroup with respect to the norm. -/
def nullSubgroup : AddSubgroup M where
  carrier := {x : M | ‖x‖ = 0}
  add_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_add_le x y).trans_eq ?_
    rw [hx, hy, add_zero]
  zero_mem' := norm_zero
  neg_mem' {x} (hx : ‖x‖ = 0) := by
    simp only [mem_setOf_eq, norm_neg]
    exact hx

@[simp]
lemma mem_nullSubgroup_iff {x : M} : x ∈ nullSubgroup ↔ ‖x‖ = 0 := Iff.rfl

lemma inseparable_iff_norm_zero (x y : M) : Inseparable x y ↔ ‖x - y‖ = 0 := by
  rw [Metric.inseparable_iff, dist_eq_norm]

lemma isClosed_nullSubgroup : IsClosed (@nullSubgroup M _ : Set M) :=
  isClosed_singleton.preimage continuous_norm

instance : Nonempty (@nullSubgroup M _) := ⟨0⟩

variable (x : SeparationQuotient M)

variable (z : M)

/-- The norm of the image of `m : M` in the quotient by the null space is zero if and only if `m`
belongs to the null space. -/
theorem quotient_norm_eq_zero_iff (m : M) :
    ‖mk m‖ = 0 ↔ ‖m‖ = 0 := by
  rw [norm_mk]

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSubgroup`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ ‖m‖ = 0 := by
  rw [← quotient_norm_eq_zero_iff]
  exact Iff.symm norm_eq_zero

end SeparationQuotient

end
