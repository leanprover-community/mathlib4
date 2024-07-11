/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Logic.Nontrivial.Basic

#align_import algebra.group.ulift from "leanprover-community/mathlib"@"564bcc44d2b394a50c0cd6340c14a6b02a50a99a"

/-!
# `ULift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `MulEquiv.ulift : ULift R ≃* R` (and its additive analogue).
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

universe u v

variable {α : Type u} {β : Type*} {x y : ULift.{v} α}

namespace ULift

@[to_additive]
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩
#align ulift.has_one ULift.one
#align ulift.has_zero ULift.zero

@[to_additive (attr := simp)]
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl
#align ulift.one_down ULift.one_down
#align ulift.zero_down ULift.zero_down

@[to_additive]
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩
#align ulift.has_mul ULift.mul
#align ulift.has_add ULift.add

@[to_additive (attr := simp)]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl
#align ulift.mul_down ULift.mul_down
#align ulift.add_down ULift.add_down

@[to_additive]
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩
#align ulift.has_div ULift.div
#align ulift.has_sub ULift.sub

@[to_additive (attr := simp)]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl
#align ulift.div_down ULift.div_down
#align ulift.sub_down ULift.sub_down

@[to_additive]
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩
#align ulift.has_inv ULift.inv
#align ulift.has_neg ULift.neg

@[to_additive (attr := simp)]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl
#align ulift.inv_down ULift.inv_down
#align ulift.neg_down ULift.neg_down

@[to_additive]
instance smul [SMul α β] : SMul α (ULift β) :=
  ⟨fun n x => up (n • x.down)⟩
#align ulift.has_smul ULift.smul
#align ulift.has_vadd ULift.vadd

@[to_additive (attr := simp)]
theorem smul_down [SMul α β] (a : α) (b : ULift.{v} β) : (a • b).down = a • b.down :=
  rfl
#align ulift.smul_down ULift.smul_down
#align ulift.vadd_down ULift.vadd_down

@[to_additive existing (reorder := 1 2) smul]
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩
#align ulift.has_pow ULift.pow

@[to_additive existing (attr := simp) (reorder := 1 2) smul_down]
theorem pow_down [Pow α β] (a : ULift.{v} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl
#align ulift.pow_down ULift.pow_down

/-- The multiplicative equivalence between `ULift α` and `α`.
-/
@[to_additive "The additive equivalence between `ULift α` and `α`."]
def _root_.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }
#align mul_equiv.ulift MulEquiv.ulift

-- Porting note: below failed due to error above, manually added
--@[to_additive]
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl
#align ulift.semigroup ULift.semigroup

instance addSemigroup [AddSemigroup α] : AddSemigroup (ULift α) :=
  (Equiv.ulift.injective.addSemigroup _) fun _ _ => rfl
#align ulift.add_semigroup ULift.addSemigroup


@[to_additive]
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl
#align ulift.comm_semigroup ULift.commSemigroup
#align ulift.add_comm_semigroup ULift.addCommSemigroup

@[to_additive]
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)
#align ulift.mul_one_class ULift.mulOneClass
#align ulift.add_zero_class ULift.addZeroClass

@[to_additive]
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid ULift.monoid
#align ulift.add_monoid ULift.addMonoid

@[to_additive]
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid ULift.commMonoid
#align ulift.add_comm_monoid ULift.addCommMonoid

instance instNatCast [NatCast α] : NatCast (ULift α) := ⟨(up ·)⟩
instance instIntCast [IntCast α] : IntCast (ULift α) := ⟨(up ·)⟩
#align ulift.has_nat_cast ULift.instNatCast
#align ulift.has_int_cast ULift.instIntCast

@[simp, norm_cast]
theorem up_natCast [NatCast α] (n : ℕ) : up (n : α) = n :=
  rfl
#align ulift.up_nat_cast ULift.up_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem up_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    up (no_index (OfNat.ofNat n : α)) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem up_intCast [IntCast α] (n : ℤ) : up (n : α) = n :=
  rfl
#align ulift.up_int_cast ULift.up_intCast

@[simp, norm_cast]
theorem down_natCast [NatCast α] (n : ℕ) : down (n : ULift α) = n :=
  rfl
#align ulift.down_nat_cast ULift.down_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem down_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    down (no_index (OfNat.ofNat n : ULift α)) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem down_intCast [IntCast α] (n : ℤ) : down (n : ULift α) = n :=
  rfl
#align ulift.down_int_cast ULift.down_intCast

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (ULift α) :=
  { ULift.one, ULift.addMonoid with
      natCast := (⟨·⟩)
      natCast_zero := congr_arg ULift.up Nat.cast_zero,
      natCast_succ := fun _ => congr_arg ULift.up (Nat.cast_succ _) }
#align ulift.add_monoid_with_one ULift.addMonoidWithOne

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addCommMonoid with }
#align ulift.add_comm_monoid_with_one ULift.addCommMonoidWithOne

@[to_additive]
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α) :=
  Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.div_inv_monoid ULift.divInvMonoid
#align ulift.sub_neg_add_monoid ULift.subNegAddMonoid

@[to_additive]
instance group [Group α] : Group (ULift α) :=
  Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.group ULift.group
#align ulift.add_group ULift.addGroup

@[to_additive]
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group ULift.commGroup
#align ulift.add_comm_group ULift.addCommGroup

instance addGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addGroup with
      intCast := (⟨·⟩),
      intCast_ofNat := fun _ => congr_arg ULift.up (Int.cast_natCast _),
      intCast_negSucc := fun _ => congr_arg ULift.up (Int.cast_negSucc _) }
#align ulift.add_group_with_one ULift.addGroupWithOne

instance addCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne (ULift α) :=
  { ULift.addGroupWithOne, ULift.addCommGroup with }
#align ulift.add_comm_group_with_one ULift.addCommGroupWithOne

@[to_additive]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl
#align ulift.left_cancel_semigroup ULift.leftCancelSemigroup
#align ulift.add_left_cancel_semigroup ULift.addLeftCancelSemigroup

@[to_additive]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl
#align ulift.right_cancel_semigroup ULift.rightCancelSemigroup
#align ulift.add_right_cancel_semigroup ULift.addRightCancelSemigroup

@[to_additive]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.left_cancel_monoid ULift.leftCancelMonoid
#align ulift.add_left_cancel_monoid ULift.addLeftCancelMonoid

@[to_additive]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.right_cancel_monoid ULift.rightCancelMonoid
#align ulift.add_right_cancel_monoid ULift.addRightCancelMonoid

@[to_additive]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_monoid ULift.cancelMonoid
#align ulift.add_cancel_monoid ULift.addCancelMonoid

@[to_additive]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_comm_monoid ULift.cancelCommMonoid
#align ulift.add_cancel_comm_monoid ULift.addCancelCommMonoid

instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.injective.nontrivial
#align ulift.nontrivial ULift.nontrivial

-- TODO we don't do `OrderedCancelCommMonoid` or `OrderedCommGroup`
-- We'd need to add instances for `ULift` in `Order.Basic`.
end ULift
