/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

-- TODO modify doc, check if instances are really needed, golf
-- want to define liftCLM. problem: a CLM on a normed vector space
-- is not automatically a `NormedAddGroupHom


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

lemma inseparable_iff_norm_zero (x y : M) : Inseparable x y ↔ ‖x - y‖ = 0 := by
  rw [Metric.inseparable_iff, dist_eq_norm]

lemma isClosed_nullSubgroup : IsClosed (@nullSubgroup M _ : Set M) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [Metric.mem_nhds_iff]
  use ‖x‖ / 2
  have : 0 < ‖x‖ := by
    apply Ne.lt_of_le _ (norm_nonneg x)
    exact fun a ↦ hx (id (Eq.symm a))
  constructor
  · exact half_pos this
  · intro y hy
    simp only [mem_ball, dist_eq_norm] at hy
    have : ‖x‖ / 2 < ‖y‖ := by
      calc ‖x‖ / 2  = ‖x‖ - ‖x‖ / 2 := by ring
      _ < ‖x‖ - ‖y - x‖ := by exact sub_lt_sub_left hy ‖x‖
      _ = ‖x‖ - ‖x - y‖ := by rw [← norm_neg (y-x), ← neg_sub y x]
      _ ≤ ‖x - (x - y)‖ := by exact norm_sub_norm_le x (x - y)
      _ = ‖y‖ := by rw [sub_sub_self x y]
    exact ne_of_gt (lt_of_le_of_lt (div_nonneg (norm_nonneg x) (zero_le_two)) this)

instance : Nonempty (@nullSubgroup M _) := ⟨0⟩

variable (x : SeparationQuotient M)

variable (z : M)

/-- The norm of the image of `m : M` in the quotient by the null space is zero if and only if `m`
belongs to the null space. -/
theorem quotient_norm_eq_zero_iff (m : M) :
    ‖mk m‖ = 0 ↔ m ∈ nullSubgroup := by
  rw [norm_mk]
  exact Eq.to_iff rfl

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSubgroup`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ m ∈ nullSubgroup := by
  rw [← quotient_norm_eq_zero_iff]
  exact Iff.symm norm_eq_zero

open NormedAddGroupHom

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
  rw[ker, normedMk]
  simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mk_toAddMonoidHom]
  ext x
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, mkAddGroupHom_apply]
  exact mk_eq_zero_iff x

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖(@normedMk M _)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp only [normedMk.apply, norm_mk,
    one_mul, le_refl]

lemma eq_of_inseparable (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSubgroup, f x = 0) :
    ∀ x y, Inseparable x y → f x = f y := by
  intro x y h
  rw [inseparable_iff_norm_zero] at h
  apply eq_of_sub_eq_zero
  rw [← map_sub f x y]
  exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSubgroup, f x = 0) : NormedAddGroupHom (SeparationQuotient M) N :=
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
theorem liftNormedAddGroupHom_apply (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSubgroup, f x = 0)
    (x : M) : liftNormedAddGroupHom f hf (normedMk x) = f x := rfl

theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSubgroup, f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨x', hx'⟩ := surjective_mk x
  rw [← hx']
  simp only [coe_toAddMonoidHom, lift_mk, norm_mk]
  exact le_opNorm f x'

theorem liftNormedAddGroupHom_unique {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ nullSubgroup, f s = 0)
    (g : NormedAddGroupHom (SeparationQuotient M) N) (h : g.comp normedMk = f) :
    g = liftNormedAddGroupHom f hf := by
  ext x
  rcases surjective_normedMk x with ⟨x, rfl⟩
  change g.comp normedMk x = _
  simp only [h]
  rfl

theorem norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ nullSubgroup, f s = 0) :
    ‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

theorem liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ nullSubgroup, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖liftNormedAddGroupHom f hf‖ ≤ c :=
  (norm_liftNormedAddGroupHom_le f hf).trans fb

theorem liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ nullSubgroup, f s = 0) (fb : f.NormNoninc) :
    (liftNormedAddGroupHom f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using NormedAddGroupHom.le_of_opNorm_le _
    (liftNormedAddGroupHom_norm_le f _ fb') _

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

end SeparationQuotientAddGroup
