/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Ring.Basic

#align_import algebra.hom.group_instances from "leanprover-community/mathlib"@"2ed7e4aec72395b6a7c3ac4ac7873a7a43ead17c"

/-!
# Instances on spaces of monoid and group morphisms

This file does two things involving `AddMonoid.End` and `Ring`.
They are separate, and if someone would like to split this file in two that may be helpful.

* We provide the `Ring` structure on `AddMonoid.End`.
* Results about `AddMonoid.End R` when `R` is a ring.
-/


universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

namespace AddMonoid.End

instance instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.End M) where
  natCast n := n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
lemma natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl
#align add_monoid.End.nat_cast_apply AddMonoid.End.natCast_apply

-- See note [no_index around OfNat.ofNat]
@[simp] lemma ofNat_apply [AddCommMonoid M] (n : ℕ) [n.AtLeastTwo] (m : M) :
    (no_index (OfNat.ofNat n : AddMonoid.End M)) m = n • m := rfl

instance instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  { AddMonoid.End.monoid M, AddMonoidHom.addCommMonoid, AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl }

instance instRing [AddCommGroup M] : Ring (AddMonoid.End M) :=
  { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

end AddMonoid.End

/-!
### Miscellaneous definitions

This file used to import `Algebra.GroupPower.Basic`, hence it was not possible to import it in
some of the lower-level files like `Algebra.Ring.Basic`. The following lemmas should be rehomed now
that `Algebra.GroupPower.Basic` was deleted.
-/


section Semiring

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both arguments.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoidHom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgHom.mul`
and `Algebra.lmul`.
-/
def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' a b := AddMonoidHom.ext <| add_mul a b
#align add_monoid_hom.mul AddMonoidHom.mul

theorem AddMonoidHom.mul_apply (x y : R) : AddMonoidHom.mul x y = x * y :=
  rfl
#align add_monoid_hom.mul_apply AddMonoidHom.mul_apply

@[simp]
theorem AddMonoidHom.coe_mul : ⇑(AddMonoidHom.mul : R →+ R →+ R) = AddMonoidHom.mulLeft :=
  rfl
#align add_monoid_hom.coe_mul AddMonoidHom.coe_mul

@[simp]
theorem AddMonoidHom.coe_flip_mul :
    ⇑(AddMonoidHom.mul : R →+ R →+ R).flip = AddMonoidHom.mulRight :=
  rfl
#align add_monoid_hom.coe_flip_mul AddMonoidHom.coe_flip_mul

/-- An `AddMonoidHom` preserves multiplication if pre- and post- composition with
`AddMonoidHom.mul` are equivalent. By converting the statement into an equality of
`AddMonoidHom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
theorem AddMonoidHom.map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (AddMonoidHom.mul : R →+ R →+ R).compr₂ f = (AddMonoidHom.mul.comp f).compl₂ f :=
  Iff.symm AddMonoidHom.ext_iff₂
#align add_monoid_hom.map_mul_iff AddMonoidHom.map_mul_iff

lemma AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute {a : R} :
    mulLeft a = mulRight a ↔ ∀ b, Commute a b :=
  DFunLike.ext_iff

lemma AddMonoidHom.mulRight_eq_mulLeft_iff_forall_commute {b : R} :
    mulRight b = mulLeft b ↔ ∀ a, Commute a b :=
  DFunLike.ext_iff

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`. -/
@[simps!]
def AddMonoid.End.mulLeft : R →+ AddMonoid.End R :=
  AddMonoidHom.mul
#align add_monoid.End.mul_left AddMonoid.End.mulLeft
#align add_monoid.End.mul_left_apply_apply AddMonoid.End.mulLeft_apply_apply

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`. -/
@[simps!]
def AddMonoid.End.mulRight : R →+ AddMonoid.End R :=
  (AddMonoidHom.mul : R →+ AddMonoid.End R).flip
#align add_monoid.End.mul_right AddMonoid.End.mulRight
#align add_monoid.End.mul_right_apply_apply AddMonoid.End.mulRight_apply_apply

end Semiring

section CommSemiring

variable {R S : Type*} [NonUnitalNonAssocCommSemiring R]

namespace AddMonoid.End

lemma mulRight_eq_mulLeft : mulRight = (mulLeft : R →+ AddMonoid.End R) :=
  AddMonoidHom.ext fun _ =>
    Eq.symm <| AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

end AddMonoid.End

end CommSemiring
