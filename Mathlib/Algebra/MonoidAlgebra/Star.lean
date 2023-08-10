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
  star f := ⟨f.support.map (Equiv.inv G), star ∘ f ∘ Inv.inv, fun x ↦ by
    simp only [Finset.mem_map_equiv, Finsupp.mem_support_iff, Function.comp_apply, star_ne_zero,
      Equiv.inv_symm, Equiv.inv_apply]⟩
  star_involutive := fun f ↦ Finsupp.ext fun x ↦ by simp
  star_mul := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [MonoidAlgebra.mul_apply, MonoidAlgebra.mul_apply]
    simp only [Finsupp.sum, star_sum, apply_ite, star_mul, star_zero, Finsupp.coe_mk,
      Function.comp_apply, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.inv_apply, inv_inv]
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
  star f := ⟨f.support.map (Equiv.neg G), star ∘ f ∘ Neg.neg, fun x ↦ by
    simp only [Finset.mem_map_equiv, Finsupp.mem_support_iff, Function.comp_apply, star_ne_zero,
      Equiv.neg_symm, Equiv.neg_apply]⟩
  star_involutive := fun f ↦ Finsupp.ext fun x ↦ by simp
  star_mul := fun f g ↦ Finsupp.ext fun x ↦ by
    simp only [Finsupp.coe_mk, Function.comp_apply]
    rw [AddMonoidAlgebra.mul_apply, AddMonoidAlgebra.mul_apply]
    simp only [Finsupp.sum, star_sum, apply_ite, star_mul, star_zero, Finsupp.coe_mk,
      Function.comp_apply, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, neg_neg]
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
