/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.nonneg.floor
! leanprover-community/mathlib commit b3f4f007a962e3787aa0f3b5c7942a1317f7d88e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Nonneg.Ring
import Mathbin.Algebra.Order.Archimedean

/-!
# Nonnegative elements are archimedean

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `floor_semiring` if `α` is.
-/


namespace Nonneg

variable {α : Type _}

/- warning: nonneg.archimedean -> Nonneg.archimedean is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : Archimedean.{u1} α _inst_1], Archimedean.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))))) x)) (Nonneg.orderedAddCommMonoid.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : Archimedean.{u1} α _inst_1], Archimedean.{u1} (Subtype.{succ u1} α (fun (x : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) x)) (Nonneg.orderedAddCommMonoid.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align nonneg.archimedean Nonneg.archimedeanₓ'. -/
instance archimedean [OrderedAddCommMonoid α] [Archimedean α] : Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : α) (hy : (0 : α) < y)
    ⟨n, show (x : α) ≤ (n • y : { x : α // 0 ≤ x }) by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩
#align nonneg.archimedean Nonneg.archimedean

/- warning: nonneg.floor_semiring -> Nonneg.floorSemiring is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1], FloorSemiring.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1], FloorSemiring.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align nonneg.floor_semiring Nonneg.floorSemiringₓ'. -/
instance floorSemiring [OrderedSemiring α] [FloorSemiring α] : FloorSemiring { r : α // 0 ≤ r }
    where
  floor a := ⌊(a : α)⌋₊
  ceil a := ⌈(a : α)⌉₊
  floor_of_neg a ha := FloorSemiring.floor_of_neg ha
  gc_floor a n ha :=
    by
    refine' (FloorSemiring.gc_floor (show 0 ≤ (a : α) from ha)).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_nat_cast]
  gc_ceil a n := by
    refine' (FloorSemiring.gc_ceil (a : α) n).trans _
    rw [← Subtype.coe_le_coe, Nonneg.coe_nat_cast]
#align nonneg.floor_semiring Nonneg.floorSemiring

/- warning: nonneg.nat_floor_coe -> Nonneg.nat_floor_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1] (a : Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)), Eq.{1} Nat (Nat.floor.{u1} α _inst_1 _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (coeSubtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r))))) a)) (Nat.floor.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1) (Nonneg.floorSemiring.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1] (a : Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r)), Eq.{1} Nat (Nat.floor.{u1} α _inst_1 _inst_2 (Subtype.val.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r) a)) (Nat.floor.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1) (Nonneg.floorSemiring.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align nonneg.nat_floor_coe Nonneg.nat_floor_coeₓ'. -/
@[norm_cast]
theorem nat_floor_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌊(a : α)⌋₊ = ⌊a⌋₊ :=
  rfl
#align nonneg.nat_floor_coe Nonneg.nat_floor_coe

/- warning: nonneg.nat_ceil_coe -> Nonneg.nat_ceil_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1] (a : Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)), Eq.{1} Nat (Nat.ceil.{u1} α _inst_1 _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) α (coeSubtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r))))) a)) (Nat.ceil.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1) (Nonneg.floorSemiring.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : FloorSemiring.{u1} α _inst_1] (a : Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r)), Eq.{1} Nat (Nat.ceil.{u1} α _inst_1 _inst_2 (Subtype.val.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r) a)) (Nat.ceil.{u1} (Subtype.{succ u1} α (fun (r : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) r)) (Nonneg.orderedSemiring.{u1} α _inst_1) (Nonneg.floorSemiring.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align nonneg.nat_ceil_coe Nonneg.nat_ceil_coeₓ'. -/
@[norm_cast]
theorem nat_ceil_coe [OrderedSemiring α] [FloorSemiring α] (a : { r : α // 0 ≤ r }) :
    ⌈(a : α)⌉₊ = ⌈a⌉₊ :=
  rfl
#align nonneg.nat_ceil_coe Nonneg.nat_ceil_coe

end Nonneg

