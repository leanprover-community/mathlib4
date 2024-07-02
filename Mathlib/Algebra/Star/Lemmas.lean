/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.GroupAction.Opposite

#align_import algebra.star.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star monoids, rings, and modules

XXX
-/

assert_not_exists Finset
assert_not_exists Subgroup
assert_not_exists Rat.instField

universe u

open MulOpposite

variable {R : Type u}

/-- `star` as a `MulAut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }
#align star_mul_aut starMulAut
#align star_mul_aut_apply starMulAut_apply

/-- `star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }
#align star_ring_equiv starRingEquiv
#align star_ring_equiv_apply starRingEquiv_apply

section

end

section CommSemiring
variable [CommSemiring R] [StarRing R]

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut : RingAut R := { starAddEquiv, starMulAut (R := R) with toFun := star }
#align star_ring_aut starRingAut
#align star_ring_aut_apply starRingAut_apply

variable (R)

/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
def starRingEnd : R →+* R := @starRingAut R _ _
#align star_ring_end starRingEnd

variable {R}

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

/-- This is not a simp lemma, since we usually want simp to keep `starRingEnd` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl
#align star_ring_end_apply starRingEnd_apply

/- Porting note (#11119): removed `simp` attribute due to report by linter:

simp can prove this:
  by simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
 -/
-- @[simp]
theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x
#align star_ring_end_self_apply starRingEnd_self_apply

instance RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (S →+* R) where
  toStar := { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]
#align ring_hom.has_involutive_star RingHom.involutiveStar

theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl
#align ring_hom.star_def RingHom.star_def

theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S →+* R) (s : S) :
    star f s = star (f s) := rfl
#align ring_hom.star_apply RingHom.star_apply

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply
#align complex.conj_conj Complex.conj_conj

alias RCLike.conj_conj := starRingEnd_self_apply
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_conj RCLike.conj_conj

open scoped ComplexConjugate

@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _

end CommSemiring

@[simp]
theorem star_inv' [DivisionSemiring R] [StarRing R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm
#align star_inv' star_inv'

@[simp]
theorem star_zpow₀ [DivisionSemiring R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm
#align star_zpow₀ star_zpow₀

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Semifield R] [StarRing R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def, op_div, mul_comm, star_mul, star_inv', op_mul, op_inv]
#align star_div' star_div'

/-- A commutative star monoid is a star module over itself via `Monoid.toMulAction`. -/
instance StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R :=
  ⟨star_mul'⟩
#align star_semigroup.to_star_module StarMul.toStarModule

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

instance {A : Type*} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => star_smul (u : R) a⟩

end Units

protected instance Invertible.star {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := Star.star (⅟ r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
#align invertible.star Invertible.star

theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟ r) = ⅟ (star r) := by
  have : star (⅟ r) = star (⅟ r) * ((star r) * ⅟ (star r)) := by
    simp only [mul_invOf_self, mul_one]
  rw [this, ← mul_assoc]
  have : (star (⅟ r)) * (star r) = star 1 := by rw [← star_mul, mul_invOf_self]
  rw [this, star_one, one_mul]
#align star_inv_of star_invOf


namespace MulOpposite

instance [Semiring R] [StarRing R] : StarRing Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`Monoid.toOppositeMulAction`. -/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] :
    StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
#align star_semigroup.to_opposite_star_module StarSemigroup.toOpposite_starModule
