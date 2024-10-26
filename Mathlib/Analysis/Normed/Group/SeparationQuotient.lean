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
All the following definitions are in the `SeparationQuotient` namespace. Hence we can access
`SeparationQuotient.normedMk` as `normedMk`.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `liftNormedAddGroupHom` : implements the universal property of `SeparationQuotient M`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ x : M, ‖x‖ = 0 → f x = 0)` and
    `liftNormedAddGroupHom f hf : NormedAddGroupHom (SeparationQuotient M) N`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `liftNormedAddGroupHom_unique` : characterizes `liftNormedAddGroupHom f hf` by the property that
its composition with `normedMk` is equal to `f`.

* `norm_liftNormedAddGroupHom_le` : `‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖`.

## Implementation details

For any `SeminormedAddCommGroup M`, we define a norm on `SeparationQuotient M` by
`‖x‖ = ‖mk x‖` using the lift.

-/


noncomputable section

open SeparationQuotient NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

variable (x : SeparationQuotient M) (z : M)

/-- For `(m : M)`, `mk m = 0` if and only if `‖m‖ = 0`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ ‖m‖ = 0 := by
  rw [← norm_mk, norm_eq_zero]

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the inseparable setoid. -/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) :=
  { mkAddMonoidHom with
    bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      mkAddMonoidHom_apply, norm_mk, one_mul, le_refl]⟩}

/-- `normedMk` agrees with `SeparationQuotient.mk`. -/
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

/-- For a norm-continuous group homomorphism `f`, its lift to the separation quotient
is bounded by the norm of `f`-/
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

/-- The operator norm of the projection is `1` if there is an element whose norm is different from
`0`. -/
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

/-- The operator norm of the projection is `0` if all the elements have norm `0`. -/
theorem norm_trivial_separationQuotient_mk (h : ∀ x : M, ‖x‖ = 0) :
    ‖@normedMk M _‖ = 0 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ (le_refl 0)
  · intro x
    simp only [normedMk.apply, zero_mul, norm_le_zero_iff]
    exact (mk_eq_zero_iff x).mpr (h x)
  · exact fun N => fun hN => fun _ => hN

end SeparationQuotient
