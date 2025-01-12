/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
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

* `norm_normedMk_eq_one : the operator norm of the projection is `1` if the subspace is not `⊤`.

* `norm_liftNormedAddGroupHom_le` : `‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖`.


-/


noncomputable section

open SeparationQuotient NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the inseparable setoid. -/
@[simps]
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) where
  __ := mkAddMonoidHom
  bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    mkAddMonoidHom_apply, norm_mk, one_mul, le_refl]⟩

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖normedMk (M := M)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp only [normedMk_apply,
    ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mkAddMonoidHom_apply, norm_mk, one_mul,
    le_refl]

lemma eq_of_inseparable (f : NormedAddGroupHom M N) (hf : ∀ x, ‖x‖ = 0 → f x = 0) :
    ∀ x y, Inseparable x y → f x = f y :=
  fun x y h ↦ eq_of_sub_eq_zero <| by
    rw [← map_sub]
    rw [Metric.inseparable_iff, dist_eq_norm] at h
    exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
@[simps]
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : NormedAddGroupHom (SeparationQuotient M) N :=
  { SeparationQuotient.liftContinuousAddMonoidHom f
      <| eq_of_inseparable f hf with
    bound' := by
      refine ⟨‖f‖, fun v ↦ ?_⟩
      obtain ⟨v, rfl⟩ := surjective_mk v
      exact le_opNorm f v }

theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

/-- The equivalence between `NormedAddGroupHom M N` vanishing on the inseparable setoid and
`NormedAddGroupHom (SeparationQuotient M) N`. -/
@[simps]
def liftNormedAddGroupHom_equiv {N : Type*} [SeminormedAddCommGroup N] :
    {f : NormedAddGroupHom M N // ∀ x, ‖x‖ = 0 → f x = 0} ≃
    NormedAddGroupHom (SeparationQuotient M) N where
  toFun f := liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk, norm_eq_zero] at hx
    simp [hx]⟩
  left_inv _ := rfl
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
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
  have fb' : ‖f‖ ≤ 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

/-- The operator norm of the projection is `1` if there is an element whose norm is different from
`0`. -/
theorem norm_normedMk_eq_one (h : ∃ x : M, ‖x‖ ≠ 0) :
    ‖normedMk (M := M)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simp only [normedMk_apply, one_mul]
    exact fun x ↦ Preorder.le_refl ‖SeparationQuotient.mk x‖
  · simp only [ge_iff_le, normedMk_apply]
    intro N _ hle
    obtain ⟨x, hxnn⟩ := h
    have : 0 < ‖x‖ := Ne.lt_of_le (Ne.symm hxnn) (norm_nonneg x)
    exact one_le_of_le_mul_right₀ this (hle x)

/-- The the projection is `0` if all the elements have norm `0`. -/
theorem normedMk_eq_zero (h : ∀ x : M, ‖x‖ = 0) :
    normedMk (M := M) = 0 := by
  ext x
  simp only [normedMk_apply, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mkAddMonoidHom_apply,
    zero_apply]
  rw [← norm_eq_zero, norm_mk]
  exact h x

end SeparationQuotient
