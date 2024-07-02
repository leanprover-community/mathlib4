/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Mathlib.Algebra.Star.Defs
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.star.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

assert_not_exists Finset
assert_not_exists Subgroup
assert_not_exists Rat.instField

universe u v

open MulOpposite

variable {R : Type u}

section StarMul

variable [Mul R] [StarMul R]

@[simp]
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]
#align semiconj_by_star_star_star semiconjBy_star_star_star

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star
#align semiconj_by.star_star_star SemiconjBy.star_star_star

@[simp]
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star
#align commute_star_star commute_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star
#align commute.star_star Commute.star_star

theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]
#align commute_star_comm commute_star_comm

end StarMul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommSemigroup R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)
#align star_mul' star_mul'

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }
#align star_mul_equiv starMulEquiv
#align star_mul_equiv_apply starMulEquiv_apply

variable (R)

@[simp]
theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm
#align star_one star_one

variable {R}

@[simp]
theorem star_pow [Monoid R] [StarMul R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm
#align star_pow star_pow

@[simp]
theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm
#align star_inv star_inv

@[simp]
theorem star_zpow [Group R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm
#align star_zpow star_zpow

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y := by
  simp [div_eq_inv_mul]
#align star_div star_div

/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starMulOfComm {R : Type*} [CommMonoid R] : StarMul R := starMulOfMulComm mul_comm
#align star_semigroup_of_comm starMulOfComm

section

attribute [local instance] starMulOfComm

/-- Note that since `starMulOfComm` is reducible, `simp` can already prove this. -/
theorem star_id_of_comm {R : Type*} [CommSemiring R] {x : R} : star x = x :=
  rfl
#align star_id_of_comm star_id_of_comm

end

/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.  -/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_add_monoid StarAddMonoid

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `AddEquiv` -/
@[simps apply]
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_add' := star_add }
#align star_add_equiv starAddEquiv
#align star_add_equiv_apply starAddEquiv_apply

variable (R)

@[simp]
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero
#align star_zero star_zero

variable {R}

@[simp]
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff (M := R)
#align star_eq_zero star_eq_zero

theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 := by
  simp only [ne_eq, star_eq_zero]
#align star_ne_zero star_ne_zero

@[simp]
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _
#align star_neg star_neg

@[simp]
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _
#align star_sub star_sub

@[simp]
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _
#align star_nsmul star_nsmul

@[simp]
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _
#align star_zsmul star_zsmul

/-- A `*`-ring `R` is a non-unital, non-associative (semi)ring with an involutive `star` operation
which is additive which makes `R` with its multiplicative structure into a `*`-multiplication
(i.e. `star (r * s) = star s * star r`).  -/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_ring StarRing

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add
#align star_ring.to_star_add_monoid StarRing.toStarAddMonoid

@[simp, norm_cast]
theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : ℕ) : star (n : R) = n := by
  rw [← nsmul_one, star_nsmul, star_one]
#align star_nat_cast star_natCast

@[simp]
theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : ℕ) [n.AtLeastTwo] :
    star (no_index (OfNat.ofNat n) : R) = OfNat.ofNat n :=
  star_natCast _

section

@[simp, norm_cast]
theorem star_intCast [Ring R] [StarRing R] (z : ℤ) : star (z : R) = z := by
  rw [← zsmul_one, star_zsmul (R := R), star_one]
#align star_int_cast star_intCast

end

#noalign star_bit0
#noalign star_bit1

/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }
#align star_ring_of_comm starRingOfComm

instance Nat.instStarRing : StarRing ℕ := starRingOfComm
instance Int.instStarRing : StarRing ℤ := starRingOfComm

/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[Semiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]`, and that
the statement only requires `[Star R] [Star A] [SMul R A]`.

If used as `[CommRing R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]`, this represents a
star algebra.
-/

class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  /-- `star` commutes with scalar multiplication -/
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a
#align star_module StarModule

export StarModule (star_smul)

attribute [simp] star_smul

instance StarAddMonoid.toStarModuleNat {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨fun n a ↦ by rw [star_nsmul, star_trivial n]⟩

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

instance : StarMul Rˣ where
  star u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl
#align units.coe_star Units.coe_star

@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl
#align units.coe_star_inv Units.coe_star_inv

end Units

protected theorem IsUnit.star [Monoid R] [StarMul R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨Star.star u, hu ▸ rfl⟩
#align is_unit.star IsUnit.star

@[simp]
theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩
#align is_unit_star isUnit_star

theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    Ring.inverse (star a) = star (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt isUnit_star.mp ha), star_zero]
#align ring.inverse_star Ring.inverse_star

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)

@[simp]
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl
#align mul_opposite.unop_star MulOpposite.unop_star

@[simp]
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl
#align mul_opposite.op_star MulOpposite.op_star

instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ where
  star_involutive r := unop_injective (star_star r.unop)

instance [Mul R] [StarMul R] : StarMul Rᵐᵒᵖ where
  star_mul x y := unop_injective (star_mul y.unop x.unop)

instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

end MulOpposite
