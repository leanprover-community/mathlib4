/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# `ULift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ULift.mul_equiv : ULift R ≃* R` (and its additive analogue).
-/


universe u v

variable {α : Type u} {β : Type _} {x y : ULift.{v} α}

namespace ULift

@[to_additive]
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩
#align ulift.has_one ULift.one
#align ulift.has_zero ULift.zero

@[simp, to_additive]
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl
#align ulift.one_down ULift.one_down
#align ulift.zero_down ULift.zero_down

@[to_additive]
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩
#align ulift.has_mul ULift.mul
#align ulift.has_add ULift.add

@[simp, to_additive]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl
#align ulift.mul_down ULift.mul_down
#align ulift.add_down ULift.add_down

@[to_additive]
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩
#align ulift.has_div ULift.div
#align ulift.has_sub ULift.sub

@[simp, to_additive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl
#align ulift.div_down ULift.div_down
#align ulift.sub_down ULift.sub_down

@[to_additive]
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩
#align ulift.has_inv ULift.inv
#align ulift.has_neg ULift.neg

@[simp, to_additive]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl
#align ulift.inv_down ULift.inv_down
#align ulift.neg_down ULift.neg_down

@[to_additive]
instance smul [SMul α β] : SMul α (ULift β) :=
  ⟨fun n x => up (n • x.down)⟩
#align ulift.has_smul ULift.smul
#align ulift.has_vadd ULift.vadd

@[simp, to_additive]
theorem smul_down [SMul α β] (a : α) (b : ULift.{v} β) : (a • b).down = a • b.down :=
  rfl
#align ulift.smul_down ULift.smul_down
#align ulift.vadd_down ULift.vadd_down

@[to_additive (reorder := 1)]
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩
#align ulift.has_pow ULift.pow

@[simp, to_additive (reorder := 1)]
theorem pow_down [Pow α β] (a : ULift.{v} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl
#align ulift.pow_down ULift.pow_down

/-- The multiplicative equivalence between `ULift α` and `α`.
-/
-- porting note: below errors: to_additive: can't transport ULift.MulEquiv.ulift to itself.
-- @[to_additive "The additive equivalence between `ULift α` and `α`."]
def MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }
#align mul_equiv.ulift ULift.MulEquiv.ulift

-- porting notes: below failed due to error above, manually added
--@[to_additive]
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl
#align ulift.semigroup ULift.semigroup
#align ulift.add_semigroup ULift.semigroup

instance addSemigroup [AddSemigroup α] : AddSemigroup (ULift α) :=
  (Equiv.ulift.injective.addSemigroup _) fun _ _ => rfl
#align add_semigroup.ulift ULift.addSemigroup


@[to_additive]
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl
#align ulift.comm_semigroup ULift.commSemigroup
#align ulift.add_comm_semigroup ULift.addCommSemigroup

@[to_additive]
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  (Equiv.ulift.injective.mulOneClass _ rfl) fun _ _ => rfl
#align ulift.mul_one_class ULift.mulOneClass
#align ulift.add_zero_class ULift.addZeroClass

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  (Equiv.ulift.injective.mulZeroOneClass _ rfl rfl) fun _ _ => rfl
#align ulift.mul_zero_one_class ULift.mulZeroOneClass

@[to_additive]
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid ULift.monoid
#align ulift.add_monoid ULift.addMonoid

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (ULift α) :=
  { ULift.one, ULift.addMonoid with
      natCast := fun n => ⟨n⟩
      natCast_zero := congr_arg ULift.up Nat.cast_zero,
      natCast_succ := fun _ => congr_arg ULift.up (Nat.cast_succ _) }
#align ulift.add_monoid_with_one ULift.addMonoidWithOne

@[simp]
theorem nat_cast_down [AddMonoidWithOne α] (n : ℕ) : (n : ULift α).down = n :=
  rfl
#align ulift.nat_cast_down ULift.nat_cast_down

@[to_additive]
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid ULift.commMonoid
#align ulift.add_comm_monoid ULift.addCommMonoid

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid_with_zero ULift.monoidWithZero

instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid_with_zero ULift.commMonoidWithZero

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

instance addGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addGroup with
      intCast := fun n => ⟨n⟩,
      intCast_ofNat := fun _ => congr_arg ULift.up (Int.cast_ofNat _),
      intCast_negSucc := fun _ => congr_arg ULift.up (Int.cast_negSucc _) }
#align ulift.add_group_with_one ULift.addGroupWithOne

@[simp]
theorem int_cast_down [AddGroupWithOne α] (n : ℤ) : (n : ULift α).down = n :=
  rfl
#align ulift.int_cast_down ULift.int_cast_down

@[to_additive]
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group ULift.commGroup
#align ulift.add_comm_group ULift.addCommGroup

instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.group_with_zero ULift.groupWithZero

instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group_with_zero ULift.commGroupWithZero

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl
#align ulift.left_cancel_semigroup ULift.leftCancelSemigroup
#align ulift.add_left_cancel_semigroup ULift.AddLeftCancelSemigroup

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl
#align ulift.right_cancel_semigroup ULift.rightCancelSemigroup
#align ulift.add_right_cancel_semigroup ULift.AddRightCancelSemigroup

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.left_cancel_monoid ULift.leftCancelMonoid
#align ulift.add_left_cancel_monoid ULift.AddLeftCancelMonoid

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.right_cancel_monoid ULift.rightCancelMonoid
#align ulift.add_right_cancel_monoid ULift.AddRightCancelMonoid

@[to_additive AddCancelMonoid]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_monoid ULift.cancelMonoid
#align ulift.add_cancel_monoid ULift.AddCancelMonoid

@[to_additive AddCancelMonoid]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_comm_monoid ULift.cancelCommMonoid
#align ulift.add_cancel_comm_monoid ULift.AddCancelMonoid

instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.injective.nontrivial
#align ulift.nontrivial ULift.nontrivial

-- TODO we don't do `OrderedCancelCommMonoid` or `OrderedCommGroup`
-- We'd need to add instances for `ULift` in `Order.Basic`.
end ULift
