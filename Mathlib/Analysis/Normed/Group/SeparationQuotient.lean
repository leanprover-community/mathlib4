/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Hom

/-!
# Lifts of maps to separation quotients of seminormed groups

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib.Analysis.Normed.Group.Uniform`.

## Main definitions

We use `M` and `N` to denote seminormed groups.
All the following definitions are in the `NullSubgroup` namespace. Hence we can access
`NullSubgroup.normedMk` as `normedMk`.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by the null subgroup.
    This is an instance so there is no need to explicitly use it.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `lift f hf`: implements the universal property of `SeparationQuotient M`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ nullSubgroup M, f s = 0)` and
    `lift f hf : NormedAddGroupHom (SeparationQuotient M) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by the null subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M`, we define a norm on `SeparationQuotient M` by
`‖x‖ = ‖mk x‖` using the lift.

-/


noncomputable section

open SeparationQuotient Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotientAddGroup

-- lemma inseparable_iff_norm_zero (x y : M) : Inseparable x y ↔ ‖x - y‖ = 0 := by
--   rw [Metric.inseparable_iff, dist_eq_norm]

variable (x : SeparationQuotient M)

variable (z : M)

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSubgroup`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ ‖m‖ = 0 := by
  rw [← norm_mk]
  exact Iff.symm norm_eq_zero

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the null space. -/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) :=
  { mkAddMonoidHom with
    bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      mkAddMonoidHom_apply, norm_mk, one_mul, le_refl]⟩}

/-- `mkAddGroupHom` agrees with `QuotientAddGroup.mk`. -/
@[simp]
theorem normedMk.apply (m : M) : normedMk m = mk m := rfl

/-- `normedMk` is surjective. -/
theorem surjective_normedMk : Function.Surjective (@normedMk M _) :=
  surjective_quot_mk _

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖(@normedMk M _)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp only [normedMk.apply, norm_mk,
    one_mul, le_refl]

lemma eq_of_inseparable (f : NormedAddGroupHom M N) (hf : ∀ x, ‖x‖ = 0 → f x = 0) :
    ∀ x y, Inseparable x y → f x = f y :=
  fun x y h ↦ eq_of_sub_eq_zero <| by
    rw [← map_sub]
    rw [Metric.inseparable_iff, dist_eq_norm] at h
    exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : NormedAddGroupHom (SeparationQuotient M) N :=
  { SeparationQuotient.liftContinuousAddMonoidHom ⟨f.toAddMonoidHom, f.continuous⟩
      <| eq_of_inseparable f hf with
    bound' := by
      use ‖f‖
      intro v
      obtain ⟨v', hv'⟩ := surjective_mk v
      rw [← hv']
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        liftContinuousAddCommMonoidHom_apply, AddMonoidHom.coe_coe, norm_mk]
      exact le_opNorm f v'}

@[simp]
theorem liftNormedAddGroupHom_apply (f : NormedAddGroupHom M N) (hf : ∀ x, ‖x‖ = 0 → f x = 0)
    (x : M) : liftNormedAddGroupHom f hf (mk x) = f x := rfl

/-- For a norm-continuous group homomorphism `f`, its lift to the separation quotient
is bounded by the norm of `f`-/
theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨x', hx'⟩ := surjective_mk x
  rw [← hx']
  simp only [coe_toAddMonoidHom, lift_mk, norm_mk]
  exact le_opNorm f x'

theorem liftNormedAddGroupHom_unique {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0)
    (g : NormedAddGroupHom (SeparationQuotient M) N) (h : g.comp normedMk = f) :
    g = liftNormedAddGroupHom f hf := by
  ext x
  rcases surjective_normedMk x with ⟨x, rfl⟩
  change g.comp normedMk x = _
  simp only [h]
  rfl

theorem norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) :
    ‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

theorem liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖liftNormedAddGroupHom f hf‖ ≤ c :=
  (norm_liftNormedAddGroupHom_le f hf).trans fb

theorem liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) (fb : f.NormNoninc) :
    (liftNormedAddGroupHom f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using NormedAddGroupHom.le_of_opNorm_le _
    (liftNormedAddGroupHom_norm_le f _ fb') _

/-- The operator norm of the projection is `1` if the null space is not dense. -/
theorem norm_normedMk (h : ∃ x : M, ‖x‖ ≠ 0) :
    ‖(@normedMk M _)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simp only [normedMk.apply, one_mul]
    exact fun x ↦ Preorder.le_refl ‖SeparationQuotient.mk x‖
  · simp only [ge_iff_le, normedMk.apply]
    intro N _ hle
    obtain ⟨x, hxnn⟩ := h
    have : 0 < ‖x‖ := Ne.lt_of_le (Ne.symm hxnn) (norm_nonneg x)
    exact one_le_of_le_mul_right₀ this (hle x)

/-- The operator norm of the projection is `0` if the null space is dense. -/
theorem norm_trivial_separationQuotient_mk (h : ∀ x : M, ‖x‖ = 0) :
    ‖@normedMk M _‖ = 0 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ (le_refl 0)
  · intro x
    simp only [normedMk.apply, zero_mul, norm_le_zero_iff]
    exact (mk_eq_zero_iff x).mpr (h x)
  · exact fun N => fun hN => fun _ => hN

end SeparationQuotientAddGroup
