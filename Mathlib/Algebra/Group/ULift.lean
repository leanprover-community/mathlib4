/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Logic.Nontrivial.Basic

/-!
# `ULift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `MulEquiv.ulift : ULift R ≃* R` (and its additive analogue).
-/

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

namespace ULift

@[to_additive]
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩

@[to_additive (attr := simp)]
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl

@[to_additive]
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩

@[to_additive (attr := simp)]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl

@[to_additive]
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[to_additive (attr := simp)]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[to_additive (attr := simp)]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

@[to_additive]
instance smul [SMul α β] : SMul α (ULift β) :=
  ⟨fun n x => up (n • x.down)⟩

@[to_additive (attr := simp)]
theorem smul_down [SMul α β] (a : α) (b : ULift.{w} β) : (a • b).down = a • b.down :=
  rfl

@[to_additive existing (reorder := 1 2) smul]
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive existing (attr := simp) (reorder := 1 2, 4 5) smul_down]
theorem pow_down [Pow α β] (a : ULift.{w} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl

/-- The multiplicative equivalence between `ULift α` and `α`.
-/
@[to_additive "The additive equivalence between `ULift α` and `α`."]
def _root_.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }

@[to_additive]
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl

@[to_additive]
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl

@[to_additive]
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)

@[to_additive]
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance instNatCast [NatCast α] : NatCast (ULift α) := ⟨(up ·)⟩
instance instIntCast [IntCast α] : IntCast (ULift α) := ⟨(up ·)⟩

@[simp, norm_cast]
theorem up_natCast [NatCast α] (n : ℕ) : up (n : α) = n :=
  rfl

@[simp]
theorem up_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    up (ofNat(n) : α) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem up_intCast [IntCast α] (n : ℤ) : up (n : α) = n :=
  rfl

@[simp, norm_cast]
theorem down_natCast [NatCast α] (n : ℕ) : down (n : ULift α) = n :=
  rfl

@[simp]
theorem down_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    down (ofNat(n) : ULift α) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem down_intCast [IntCast α] (n : ℤ) : down (n : ULift α) = n :=
  rfl

instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (ULift α) :=
  { ULift.one, ULift.addMonoid with
      natCast := (⟨·⟩)
      natCast_zero := congr_arg ULift.up Nat.cast_zero,
      natCast_succ := fun _ => congr_arg ULift.up (Nat.cast_succ _) }

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addCommMonoid with }

@[to_additive]
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α) :=
  Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance group [Group α] : Group (ULift α) :=
  Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance addGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (ULift α) :=
  { ULift.addMonoidWithOne, ULift.addGroup with
      intCast := (⟨·⟩),
      intCast_ofNat := fun _ => congr_arg ULift.up (Int.cast_natCast _),
      intCast_negSucc := fun _ => congr_arg ULift.up (Int.cast_negSucc _) }

instance addCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne (ULift α) :=
  { ULift.addGroupWithOne, ULift.addCommGroup with }

@[to_additive]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl

@[to_additive]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl

@[to_additive]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.injective.nontrivial

-- TODO we don't do `OrderedCancelCommMonoid` or `OrderedCommGroup`
-- We'd need to add instances for `ULift` in `Order.Basic`.
end ULift
