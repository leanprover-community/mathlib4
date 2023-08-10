/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.BigOperators

/-!  # The star structure on group algebras.

Given a group `G`, the inverse mapping `g ↦ g⁻¹` gives rise to an involutive star on the group
algebra `k[G]`.

We define this star here and prove that it is part of a `StarRing`. In fact more is true: this data
is part of a natural Hopf algebra structure, but we do not include this result here.

## Main statements:

 * `MonoidAlgebra.instStarRing`
 * `AddMonoidAlgebra.instStarRing`

## Implementation details:

We cater for the case that `G` carries either `Add` or `Mul` notation by making statements about
both `MonoidAlgebra` and `AddMonoidAlgebra`. As elsewhere in the monoid / group algebra
implementation, we are unfortunately unable to rely on `to_additive` to there is some undesirable
code duplication.

-/

namespace MonoidAlgebra

variable {k G : Type _} [Semiring k] [StarRing k] [DecidableEq G] [Group G]

instance instStarRing : StarRing (MonoidAlgebra k G) where
  star := fun f ↦ ⟨f.support.image Inv.inv, star ∘ f ∘ Inv.inv, fun x ↦ by
    simp only [Finset.mem_image, Finsupp.mem_support_iff, Function.comp_apply]
    refine' ⟨_, fun h ↦ ⟨x⁻¹, star_ne_zero.mp h, inv_inv x⟩⟩
    rintro ⟨y, h, rfl⟩
    rw [inv_inv]
    exact star_ne_zero.mpr h⟩
  star_involutive := fun f ↦ Finsupp.ext fun x ↦ by simp
  star_mul := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [MonoidAlgebra.mul_apply, MonoidAlgebra.mul_apply]
    simp only [Finsupp.sum, Finsupp.coe_mk, Function.comp_apply, Finsupp.mem_support_iff, ne_eq,
      inv_inj, imp_self, implies_true, forall_const, Finset.sum_image, inv_inv, star_sum, apply_ite,
      star_zero, star_mul]
    rw [Finset.sum_comm]
    simp_rw [← mul_inv_rev, inv_eq_iff_eq_inv]
  star_add := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [Finsupp.add_apply, Finsupp.add_apply]
    simp

@[simp] lemma star_apply {f : MonoidAlgebra k G} {x : G} : star f x = star (f x⁻¹) := rfl

@[simp] lemma star_smul {a : k} {f : MonoidAlgebra k G} :
    star (a • f) = (MulOpposite.op (star a)) • star f := Finsupp.ext fun x ↦ by
  rw [Finsupp.smul_apply, star_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, star_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {k G : Type _} [Semiring k] [StarRing k] [DecidableEq G] [AddGroup G]

instance instStarRing : StarRing (AddMonoidAlgebra k G) where
  star := fun f ↦ ⟨f.support.image Neg.neg, star ∘ f ∘ Neg.neg, fun x ↦ by
    simp only [Finset.mem_image, Finsupp.mem_support_iff, Function.comp_apply]
    refine' ⟨_, fun h ↦ ⟨-x, star_ne_zero.mp h, neg_neg x⟩⟩
    rintro ⟨y, h, rfl⟩
    rw [neg_neg]
    exact star_ne_zero.mpr h⟩
  star_involutive := fun f ↦ Finsupp.ext fun x ↦ by simp
  star_mul := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [AddMonoidAlgebra.mul_apply, AddMonoidAlgebra.mul_apply]
    simp only [Finsupp.sum, Finsupp.coe_mk, Function.comp_apply, Finsupp.mem_support_iff, ne_eq,
      neg_inj, imp_self, implies_true, forall_const, Finset.sum_image, neg_neg, star_sum, apply_ite,
      star_zero, star_mul]
    rw [Finset.sum_comm]
    simp_rw [← neg_add_rev, neg_eq_iff_eq_neg]
  star_add := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [Finsupp.add_apply, Finsupp.add_apply]
    simp

@[simp] lemma star_apply {f : AddMonoidAlgebra k G} {x : G} : star f x = star (f (-x)) := rfl

@[simp] lemma star_smul {a : k} {f : AddMonoidAlgebra k G} :
    star (a • f) = (MulOpposite.op (star a)) • star f := Finsupp.ext fun x ↦ by
  rw [Finsupp.smul_apply, star_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, star_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

end AddMonoidAlgebra
