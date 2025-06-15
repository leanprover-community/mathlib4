/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Opposites
import Mathlib.Tactic.Spread

/-!
# Group structures on the multiplicative and additive opposites
-/

assert_not_exists MonoidWithZero DenselyOrdered Units

variable {α : Type*}

namespace MulOpposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/

@[to_additive] instance instNatCast [NatCast α] : NatCast αᵐᵒᵖ where natCast n := op n
@[to_additive] instance instIntCast [IntCast α] : IntCast αᵐᵒᵖ where intCast n := op n

instance instAddSemigroup [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.addSemigroup _ fun _ _ => rfl

instance instAddLeftCancelSemigroup [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

instance instAddRightCancelSemigroup [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

instance instAddCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.addCommSemigroup _ fun _ _ => rfl

instance instAddZeroClass [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

instance instAddMonoid [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance instAddCommMonoid [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne αᵐᵒᵖ where
  toNatCast := instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op ↑(n : ℕ) + 1 by simp

instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  __ := instAddCommMonoid

instance instSubNegMonoid [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance instAddGroup [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

instance instAddCommGroup [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne αᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : ℤ) : α) = op (n : α) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : ℕ) : α))) by simp

instance instAddCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne αᵐᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instAddGroupWithOne

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/

@[to_additive]
instance instIsRightCancelMul [Mul α] [IsLeftCancelMul α] : IsRightCancelMul αᵐᵒᵖ where
  mul_right_cancel _ _ _ h := unop_injective <| mul_left_cancel <| op_injective h

@[to_additive]
instance instIsLeftCancelMul [Mul α] [IsRightCancelMul α] : IsLeftCancelMul αᵐᵒᵖ where
  mul_left_cancel _ _ _ h := unop_injective <| mul_right_cancel <| op_injective h

@[to_additive]
instance instSemigroup [Semigroup α] : Semigroup αᵐᵒᵖ where
  mul_assoc x y z := unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x)

@[to_additive]
instance instLeftCancelSemigroup [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
instance instRightCancelSemigroup [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵐᵒᵖ where
  mul_comm x y := unop_injective <| mul_comm (unop y) (unop x)

@[to_additive]
instance instMulOneClass [MulOneClass α] : MulOneClass αᵐᵒᵖ where
  toMul := instMul
  toOne := instOne
  one_mul _ := unop_injective <| mul_one _
  mul_one _ := unop_injective <| one_mul _

@[to_additive]
instance instMonoid [Monoid α] : Monoid αᵐᵒᵖ where
  toSemigroup := instSemigroup
  __ := instMulOneClass
  npow n a := op <| a.unop ^ n
  npow_zero _ := unop_injective <| pow_zero _
  npow_succ _ _ := unop_injective <| pow_succ' _ _

@[to_additive]
instance instLeftCancelMonoid [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instLeftCancelSemigroup

@[to_additive]
instance instRightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instRightCancelSemigroup

@[to_additive]
instance instCancelMonoid [CancelMonoid α] : CancelMonoid αᵐᵒᵖ where
  toLeftCancelMonoid := instLeftCancelMonoid
  __ := instRightCancelMonoid

@[to_additive]
instance instCommMonoid [CommMonoid α] : CommMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instCommSemigroup

@[to_additive]
instance instCancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ where
  toCommMonoid := instCommMonoid
  __ := instLeftCancelMonoid

@[to_additive AddOpposite.instSubNegMonoid]
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  toInv := instInv
  zpow n a := op <| a.unop ^ n
  zpow_zero' _ := unop_injective <| zpow_zero _
  zpow_succ' _ _ := unop_injective <| by
    rw [unop_op, zpow_natCast, pow_succ', unop_mul, unop_op, zpow_natCast]
  zpow_neg' _ _ := unop_injective <| DivInvMonoid.zpow_neg' _ _

@[to_additive]
instance instDivisionMonoid [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
  __ := instInvolutiveInv
  mul_inv_rev _ _ := unop_injective <| mul_inv_rev _ _
  inv_eq_of_mul _ _ h := unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h

@[to_additive AddOpposite.instSubtractionCommMonoid]
instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ where
  toDivisionMonoid := instDivisionMonoid
  __ := instCommSemigroup

@[to_additive]
instance instGroup [Group α] : Group αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
  inv_mul_cancel _ := unop_injective <| mul_inv_cancel _

@[to_additive]
instance instCommGroup [CommGroup α] : CommGroup αᵐᵒᵖ where
  toGroup := instGroup
  __ := instCommSemigroup

section Monoid
variable [Monoid α]

@[simp] lemma op_pow (x : α) (n : ℕ) : op (x ^ n) = op x ^ n := rfl

@[simp] lemma unop_pow (x : αᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n := rfl

end Monoid

section DivInvMonoid
variable [DivInvMonoid α]

@[simp] lemma op_zpow (x : α) (z : ℤ) : op (x ^ z) = op x ^ z := rfl

@[simp] lemma unop_zpow (x : αᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z := rfl

end DivInvMonoid

@[to_additive (attr := simp, norm_cast)]
theorem op_natCast [NatCast α] (n : ℕ) : op (n : α) = n :=
  rfl

@[to_additive (attr := simp)]
theorem op_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    op (ofNat(n) : α) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem op_intCast [IntCast α] (n : ℤ) : op (n : α) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_natCast [NatCast α] (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
theorem unop_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    unop (ofNat(n) : αᵐᵒᵖ) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_intCast [IntCast α] (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl

@[to_additive (attr := simp)]
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

@[to_additive]
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h

@[to_additive]
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h

@[to_additive]
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

instance instSemigroup [Semigroup α] : Semigroup αᵃᵒᵖ := unop_injective.semigroup _ fun _ _ ↦ rfl

instance instLeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.leftCancelSemigroup _ fun _ _ => rfl

instance instRightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.rightCancelSemigroup _ fun _ _ => rfl

instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.commSemigroup _ fun _ _ => rfl

instance instMulOneClass [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

instance pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

@[simp]
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl

@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl

instance instMonoid [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance instCommMonoid [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance instGroup [Group α] : Group αᵃᵒᵖ :=
  unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance instCommGroup [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- NOTE: `addMonoidWithOne α → addMonoidWithOne αᵃᵒᵖ` does not hold
instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵃᵒᵖ where
  toNatCast := instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op ↑(n : ℕ) + 1 by simp [add_comm]

instance instAddCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne αᵃᵒᵖ where
  toIntCast := instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
  intCast_ofNat _ := congr_arg op <| Int.cast_natCast _
  intCast_negSucc _ := congr_arg op <| Int.cast_negSucc _

end AddOpposite
