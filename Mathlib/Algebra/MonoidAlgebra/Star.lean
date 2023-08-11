/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Star.BigOperators

/-!  # The star structure on group algebras.

Given a group `G`, the inverse mapping `g ↦ g⁻¹` together with a (possibly-trivial) star on the
scalars gives rise to an involutive star on the group algebra `k[G]`.

We define this star here and prove that it satisfies the axioms of a `StarRing`. In fact more is
true: this data is part of a natural Hopf algebra structure, but we do not include this result here.

## Main statements:

 * `MonoidAlgebra.invert`
 * `AddMonoidAlgebra.invert`

## Implementation details:

We cater for the case that `G` carries either `Add` or `Mul` notation by making statements about
both `MonoidAlgebra` and `AddMonoidAlgebra`. As elsewhere in the monoid / group algebra
implementation, we are unfortunately unable to rely on `to_additive` to there is some undesirable
code duplication.

-/

namespace MonoidAlgebra

section

variable {k G : Type*} [Semiring k] [StarRing k] [DecidableEq G] [Group G]

/-- A `StarRing` structure on the group algebra.

Note that this combines the group inversion `g ↦ g⁻¹` and the star on the scalars (see
`MonoidAlgebra.star_apply`). This is necessary for the `star_mul` axiom to hold.

We do note make this an instance because in the case that the scalars and / or the group are
commutative, there are up to three natural (non-trivial) `StarRing` structures according to whether
one includes the group inversion and the star on the scalars. -/
def instStarRing : StarRing (MonoidAlgebra k G) where
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

attribute [local instance] instStarRing

@[simp] lemma star_apply {f : MonoidAlgebra k G} {x : G} : star f x = star (f x⁻¹) := rfl

@[simp] lemma star_smul {a : k} {f : MonoidAlgebra k G} :
    star (a • f) = (MulOpposite.op (star a)) • star f := Finsupp.ext fun x ↦ by
  rw [Finsupp.smul_apply, star_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, star_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

end

section Commutative

variable {k G : Type*} [CommSemiring k] [DecidableEq G] [CommGroup G]

/-- This is the natural involution on the group algebra `k[G]` induced by `g ↦ g⁻¹`. It exists
when the scalars `k` and the group `G` are both commutative. -/
noncomputable def invert : MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G :=
  mapDomainAlgEquiv k k $ MulEquiv.inv G

@[simp] lemma invert_apply {f : MonoidAlgebra k G} {x : G} : invert f x = f x⁻¹ := by
  conv_lhs => rw [← inv_inv x]
  rw [invert, mapDomainAlgEquiv_apply, ← MulEquiv.inv_apply,
    Finsupp.mapDomain_apply (MulEquiv.inv G).injective]

lemma involutive_invert : Function.Involutive (invert (k := k) (G := G)) :=
  fun f ↦ Finsupp.ext fun x ↦ by simp

/-- When both `k` and `G` are commutative, we do not need a star on `k` to obtain a `StarRing`
structure. See `MonoidAlgebra.invert` where this is bundled as an algebra equivalence. -/
def instStarRingOfCommComm {k : Type*} [CommSemiring k] : StarRing (MonoidAlgebra k G) :=
  letI : StarRing k := starRingOfComm; MonoidAlgebra.instStarRing

attribute [local instance] instStarRingOfCommComm

@[simp] lemma star_eq_invert : star (R := MonoidAlgebra k G) = invert :=
  funext fun f ↦ Finsupp.ext fun x ↦ by rw [invert_apply]; rfl

end Commutative

end MonoidAlgebra

namespace AddMonoidAlgebra

section

variable {k G : Type _} [Semiring k] [StarRing k] [DecidableEq G] [AddGroup G]

/-- A `StarRing` structure on the additive group algebra.

See `MonoidAlgebra.instStarRing` for further remarks. -/
def instStarRing : StarRing (AddMonoidAlgebra k G) where
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

attribute [local instance] instStarRing

@[simp] lemma star_apply {f : AddMonoidAlgebra k G} {x : G} : star f x = star (f (-x)) := rfl

@[simp] lemma star_smul {a : k} {f : AddMonoidAlgebra k G} :
    star (a • f) = (MulOpposite.op (star a)) • star f := Finsupp.ext fun x ↦ by
  rw [Finsupp.smul_apply, star_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, star_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

end

section Commutative

variable {k G : Type*} [CommSemiring k] [DecidableEq G] [AddCommGroup G]

/-- This is the natural involution on the group algebra `k[G]` induced by `g ↦ -g`. It exists
when the scalars `k` and the group `G` are both commutative. -/
noncomputable def invert : AddMonoidAlgebra k G ≃ₐ[k] AddMonoidAlgebra k G :=
  mapDomainAlgEquiv k k $ AddEquiv.neg G

@[simp] lemma invert_apply {f : MonoidAlgebra k G} {x : G} : invert f x = f (-x) := by
  conv_lhs => rw [← neg_neg x]
  rw [invert, mapDomainAlgEquiv_apply, ← AddEquiv.neg_apply,
    Finsupp.mapDomain_apply (AddEquiv.neg G).injective]

lemma involutive_invert : Function.Involutive (invert (k := k) (G := G)) :=
  fun f ↦ Finsupp.ext fun x ↦ by simp

/-- When both `k` and `G` are commutative, we do not need a star on `k` to obtain a `StarRing`
structure. See `MonoidAlgebra.invert` where this is bundled as an algebra equivalence. -/
def instStarRingOfCommComm {k : Type*} [CommSemiring k] : StarRing (AddMonoidAlgebra k G) :=
  letI : StarRing k := starRingOfComm; AddMonoidAlgebra.instStarRing

attribute [local instance] instStarRingOfCommComm

@[simp] lemma star_eq_invert : star (R := AddMonoidAlgebra k G) = invert :=
  funext fun f ↦ Finsupp.ext fun x ↦ by rw [invert_apply]; rfl

end Commutative

end AddMonoidAlgebra
