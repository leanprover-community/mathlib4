/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Hom

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib.Analysis.Normed.Group.Uniform`.

## Main definitions

We use `M` to denote seminormed groups.
All the following definitions are in the `NullSubgroup` namespace. Hence we can access
`NullSubgroup.normedMk` as `normedMk`.

* `nullSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

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
lemma mem_nullSubmodule_iff {x : M} : x ∈ nullSubgroup ↔ ‖x‖ = 0 := Iff.rfl

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

/-- The morphism from a seminormed group to the quotient by the null space. -/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) :=
  { mkAddGroupHom with
    bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      mkAddGroupHom_apply, norm_mk, one_mul, le_refl]⟩}

/-- `mkAddGroupHom` agrees with `QuotientAddGroup.mk`. -/
@[simp]
theorem normedMk.apply (m : M) : normedMk m = mk m := rfl

/-- `normedMk` is surjective. -/
theorem surjective_normedMk : Function.Surjective (@normedMk M _) :=
  surjective_quot_mk _

/-- The kernel of `normedMk` is `nullSubgroup`. -/
theorem ker_normedMk : (@normedMk M _).ker = nullSubgroup := by
  ext _; exact mk_eq_zero_iff _

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖(@normedMk M _)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp only [normedMk.apply, norm_mk,
    one_mul, le_refl]

/-- The operator norm of the projection is `1` if the null space is not dense. -/
theorem norm_normedMk (h : (@nullSubgroup M _ : Set M) ≠ univ) :
    ‖(@normedMk M _)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simp only [normedMk.apply, one_mul]
    exact fun x ↦ Preorder.le_refl ‖SeparationQuotient.mk x‖
  · simp only [ge_iff_le, normedMk.apply]
    intro N hN hx
    rw [← nonempty_compl] at h
    obtain ⟨x, hxnn⟩ := h
    have : 0 < ‖x‖ := Ne.lt_of_le (Ne.symm hxnn) (norm_nonneg x)
    exact one_le_of_le_mul_right₀ this (hx x)

/-- The operator norm of the projection is `0` if the null space is dense. -/
theorem norm_trivial_separationQuotient_mk (h : (@nullSubgroup M _ : Set M) = Set.univ) :
    ‖@normedMk M _‖ = 0 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ (le_refl 0)
  · intro x
    have : x ∈ nullSubgroup := by
      rw [← SetLike.mem_coe, h]
      exact trivial
    simp only [normedMk.apply, zero_mul, norm_le_zero_iff]
    exact (mk_eq_zero_iff x).mpr this
  · exact fun N => fun hN => fun _ => hN

end SeparationQuotient

end
