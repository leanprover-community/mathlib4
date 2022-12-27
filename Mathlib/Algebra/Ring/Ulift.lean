/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.ring.ulift
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Ulift
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.Ring.Equiv

/-!
# `ulift` instances for ring

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance mulZeroClass [MulZeroClass α] : MulZeroClass (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align ulift.mul_zero_class ULift.mulZeroClass

instance distrib [Distrib α] : Distrib (ULift α) := by
  refine_struct
      { add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align ulift.distrib ULift.distrib

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_non_assoc_semiring ULift.nonUnitalNonAssocSemiring

instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with 
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_assoc_semiring ULift.nonAssocSemiring

instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_semiring ULift.nonUnitalSemiring

instance semiring [Semiring α] : Semiring (ULift α) := by
  refine_struct
      { ULift.addMonoidWithOne with 
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align ulift.semiring ULift.semiring

/-- The ring equivalence between `ulift α` and `α`.
-/
def ringEquiv [NonUnitalNonAssocSemiring α] :
    ULift α ≃+* α where 
  toFun := ULift.down
  invFun := ULift.up
  map_mul' x y := rfl
  map_add' x y := rfl
  left_inv := by tidy
  right_inv := by tidy
#align ulift.ring_equiv ULift.ringEquiv

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_comm_semiring ULift.nonUnitalCommSemiring

instance commSemiring [CommSemiring α] : CommSemiring (ULift α) := by
  refine_struct
      { ULift.semiring with 
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align ulift.comm_semiring ULift.commSemiring

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_non_assoc_ring ULift.nonUnitalNonAssocRing

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_ring ULift.nonUnitalRing

instance nonAssocRing [NonAssocRing α] : NonAssocRing (ULift α) := by
  refine_struct
      { ULift.addGroupWithOne with 
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_assoc_ring ULift.nonAssocRing

instance ring [Ring α] : Ring (ULift α) := by
  refine_struct
      { ULift.semiring, ULift.addGroupWithOne with
        zero := (0 : ULift α)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.ring ULift.ring

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing (ULift α) := by
  refine_struct
      { zero := (0 : ULift α)
        add := (· + ·)
        mul := (· * ·)
        sub := Sub.sub
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align ulift.non_unital_comm_ring ULift.nonUnitalCommRing

instance commRing [CommRing α] : CommRing (ULift α) := by
  refine_struct { ULift.ring with } <;> pi_instance_derive_field
#align ulift.comm_ring ULift.commRing

instance [HasRatCast α] : HasRatCast (ULift α) :=
  ⟨fun a => ULift.up (coe a)⟩

@[simp]
theorem rat_cast_down [HasRatCast α] (n : ℚ) : ULift.down (n : ULift α) = n :=
  rfl
#align ulift.rat_cast_down ULift.rat_cast_down

instance field [Field α] : Field (ULift α) := by
  have of_rat_mk : ∀ a b h1 h2, ((⟨a, b, h1, h2⟩ : ℚ) : ULift α) = ↑a * (↑b)⁻¹ := by
    intro a b h1 h2
    ext
    rw [rat_cast_down, mul_down, inv_down, nat_cast_down, int_cast_down]
    exact Field.rat_cast_mk a b h1 h2
  refine_struct
      { @ULift.nontrivial α _, ULift.commRing with
        zero := (0 : ULift α)
        inv := Inv.inv
        div := Div.div
        zpow := fun n a => ULift.up (a.down ^ n)
        ratCast := coe
        rat_cast_mk := of_rat_mk
        qsmul := (· • ·) } <;>
    pi_instance_derive_field
  -- `mul_inv_cancel` requires special attention: it leaves the goal `∀ {a}, a ≠ 0 → a * a⁻¹ = 1`.
  cases a
  tauto
#align ulift.field ULift.field

end ULift

