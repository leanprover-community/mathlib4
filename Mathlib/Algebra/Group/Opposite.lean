/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Opposites
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread

#align_import algebra.group.opposite from "leanprover-community/mathlib"@"0372d31fb681ef40a687506bc5870fd55ebc8bb9"

/-!
# Group structures on the multiplicative and additive opposites
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

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
  toLeftCancelSemigroup := instLeftCancelSemigroup
  __ := instMonoid

@[to_additive]
instance instRightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ where
  toRightCancelSemigroup := instRightCancelSemigroup
  __ := instMonoid

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
  toLeftCancelMonoid := instLeftCancelMonoid
  __ := instCommMonoid

@[to_additive AddOpposite.instSubNegMonoid]
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  toInv := instInv
  zpow n a := op <| a.unop ^ n
  zpow_zero' _ := unop_injective <| zpow_zero _
  zpow_succ' _ _ := unop_injective <| by
    simp only [Int.ofNat_eq_coe]
    rw [unop_op, zpow_natCast, pow_succ', unop_mul, unop_op, zpow_natCast]
  zpow_neg' _ _ := unop_injective <| DivInvMonoid.zpow_neg' _ _

@[to_additive AddOpposite.instSubtractionMonoid]
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
  mul_left_inv _ := unop_injective <| mul_inv_self _

@[to_additive]
instance instCommGroup [CommGroup α] : CommGroup αᵐᵒᵖ where
  toGroup := instGroup
  __ := instCommSemigroup

section Monoid
variable [Monoid α]

@[simp] lemma op_pow (x : α) (n : ℕ) : op (x ^ n) = op x ^ n := rfl
#align mul_opposite.op_pow MulOpposite.op_pow

@[simp] lemma unop_pow (x : αᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n := rfl
#align mul_opposite.unop_pow MulOpposite.unop_pow

end Monoid

section DivInvMonoid
variable [DivInvMonoid α]

@[simp] lemma op_zpow (x : α) (z : ℤ) : op (x ^ z) = op x ^ z := rfl
#align mul_opposite.op_zpow MulOpposite.op_zpow

@[simp] lemma unop_zpow (x : αᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z := rfl
#align mul_opposite.unop_zpow MulOpposite.unop_zpow

end DivInvMonoid

@[to_additive (attr := simp, norm_cast)]
theorem op_natCast [NatCast α] (n : ℕ) : op (n : α) = n :=
  rfl
#align mul_opposite.op_nat_cast MulOpposite.op_natCast
#align add_opposite.op_nat_cast AddOpposite.op_natCast

-- See note [no_index around OfNat.ofNat]
@[to_additive (attr := simp)]
theorem op_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    op (no_index (OfNat.ofNat n : α)) = OfNat.ofNat n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem op_intCast [IntCast α] (n : ℤ) : op (n : α) = n :=
  rfl
#align mul_opposite.op_int_cast MulOpposite.op_intCast
#align add_opposite.op_int_cast AddOpposite.op_intCast

@[to_additive (attr := simp, norm_cast)]
theorem unop_natCast [NatCast α] (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_nat_cast MulOpposite.unop_natCast
#align add_opposite.unop_nat_cast AddOpposite.unop_natCast

-- See note [no_index around OfNat.ofNat]
@[to_additive (attr := simp)]
theorem unop_ofNat [NatCast α] (n : ℕ) [n.AtLeastTwo] :
    unop (no_index (OfNat.ofNat n : αᵐᵒᵖ)) = OfNat.ofNat n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem unop_intCast [IntCast α] (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_int_cast MulOpposite.unop_intCast
#align add_opposite.unop_int_cast AddOpposite.unop_intCast

@[to_additive (attr := simp)]
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl
#align mul_opposite.unop_div MulOpposite.unop_div
#align add_opposite.unop_sub AddOpposite.unop_sub

@[to_additive (attr := simp)]
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]
#align mul_opposite.op_div MulOpposite.op_div
#align add_opposite.op_sub AddOpposite.op_sub

@[to_additive (attr := simp)]
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]
#align mul_opposite.semiconj_by_op MulOpposite.semiconjBy_op
#align add_opposite.semiconj_by_op AddOpposite.addSemiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]
#align mul_opposite.semiconj_by_unop MulOpposite.semiconjBy_unop
#align add_opposite.semiconj_by_unop AddOpposite.addSemiconjBy_unop

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

@[to_additive]
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h
#align semiconj_by.op SemiconjBy.op
#align add_semiconj_by.op AddSemiconjBy.op

@[to_additive]
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h
#align semiconj_by.unop SemiconjBy.unop
#align add_semiconj_by.unop AddSemiconjBy.unop

@[to_additive]
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h
#align commute.op Commute.op
#align add_commute.op AddCommute.op

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop
#align mul_opposite.commute.unop Commute.unop
#align add_opposite.commute.unop AddCommute.unop

@[to_additive (attr := simp)]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op
#align mul_opposite.commute_op MulOpposite.commute_op
#align add_opposite.commute_op AddOpposite.addCommute_op

@[to_additive (attr := simp, nolint simpComm)]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop
#align mul_opposite.commute_unop MulOpposite.commute_unop
#align add_opposite.commute_unop AddOpposite.addCommute_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop

/-- The function `MulOpposite.op` is an additive equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true }) apply symm_apply]
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ :=
  { opEquiv with map_add' := fun _ _ => rfl }
#align mul_opposite.op_add_equiv MulOpposite.opAddEquiv
#align mul_opposite.op_add_equiv_apply MulOpposite.opAddEquiv_apply
#align mul_opposite.op_add_equiv_symm_apply MulOpposite.opAddEquiv_symm_apply

@[simp]
theorem opAddEquiv_toEquiv [Add α] : ((opAddEquiv : α ≃+ αᵐᵒᵖ) : α ≃ αᵐᵒᵖ) = opEquiv := rfl
#align mul_opposite.op_add_equiv_to_equiv MulOpposite.opAddEquiv_toEquiv

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
#align add_opposite.op_pow AddOpposite.op_pow

@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl
#align add_opposite.unop_pow AddOpposite.unop_pow

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

/-- The function `AddOpposite.op` is a multiplicative equivalence. -/
@[simps! (config := { fullyApplied := false, simpRhs := true })]
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ :=
  { opEquiv with map_mul' := fun _ _ => rfl }
#align add_opposite.op_mul_equiv AddOpposite.opMulEquiv
#align add_opposite.op_mul_equiv_symm_apply AddOpposite.opMulEquiv_symm_apply

@[simp]
theorem opMulEquiv_toEquiv [Mul α] : ((opMulEquiv : α ≃* αᵃᵒᵖ) : α ≃ αᵃᵒᵖ) = opEquiv :=
  rfl
#align add_opposite.op_mul_equiv_to_equiv AddOpposite.opMulEquiv_toEquiv

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `MulEquiv` to the opposite group. When `G` is commutative, there is
`MulEquiv.inv`. -/
@[to_additive (attr := simps! (config := { fullyApplied := false, simpRhs := true }))
      "Negation on an additive group is an `AddEquiv` to the opposite group. When `G`
      is commutative, there is `AddEquiv.inv`."]
def MulEquiv.inv' (G : Type*) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' := fun x y => unop_injective <| mul_inv_rev x y }
#align mul_equiv.inv' MulEquiv.inv'
#align add_equiv.neg' AddEquiv.neg'
#align mul_equiv.inv'_symm_apply MulEquiv.inv'_symm_apply
#align add_equiv.inv'_symm_apply AddEquiv.neg'_symm_apply

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := .asFn))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`."]
def MulHom.toOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_mul' x y := by simp [(hf x y).eq]
#align mul_hom.to_opposite MulHom.toOpposite
#align add_hom.to_opposite AddHom.toOpposite
#align mul_hom.to_opposite_apply MulHom.toOpposite_apply
#align add_hom.to_opposite_apply AddHom.toOpposite_apply

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := .asFn))
      "An additive semigroup homomorphism `f : AddHom M N` such that `f x` additively
      commutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`."]
def MulHom.fromOpposite {M N : Type*} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq
#align mul_hom.from_opposite MulHom.fromOpposite
#align add_hom.from_opposite AddHom.fromOpposite
#align mul_hom.from_opposite_apply MulHom.fromOpposite_apply
#align add_hom.from_opposite_apply AddHom.fromOpposite_apply

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := .asFn))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`."]
def MonoidHom.toOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ where
  toFun := op ∘ f
  map_one' := congrArg op f.map_one
  map_mul' x y := by simp [(hf x y).eq]
#align monoid_hom.to_opposite MonoidHom.toOpposite
#align add_monoid_hom.to_opposite AddMonoidHom.toOpposite
#align monoid_hom.to_opposite_apply MonoidHom.toOpposite_apply
#align add_monoid_hom.to_opposite_apply AddMonoidHom.toOpposite_apply

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := .asFn))
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes
      with `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`."]
def MonoidHom.fromOpposite {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' _ _ := (f.map_mul _ _).trans (hf _ _).eq
#align monoid_hom.from_opposite MonoidHom.fromOpposite
#align add_monoid_hom.from_opposite AddMonoidHom.fromOpposite
#align monoid_hom.from_opposite_apply MonoidHom.fromOpposite_apply
#align add_monoid_hom.from_opposite_apply AddMonoidHom.fromOpposite_apply

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      "The additive units of the additive opposites are equivalent to the additive opposites
      of the additive units."]
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' x y := unop_injective <| Units.ext <| rfl
  left_inv x := Units.ext <| by simp
  right_inv x := unop_injective <| Units.ext <| by rfl
#align units.op_equiv Units.opEquiv
#align add_units.op_equiv AddUnits.opEquiv

@[to_additive (attr := simp)]
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl
#align units.coe_unop_op_equiv Units.coe_unop_opEquiv
#align add_units.coe_unop_op_equiv AddUnits.coe_unop_opEquiv

@[to_additive (attr := simp)]
theorem Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) :
    (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl
#align units.coe_op_equiv_symm Units.coe_opEquiv_symm
#align add_units.coe_op_equiv_symm AddUnits.coe_opEquiv_symm

@[to_additive]
nonrec theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩
#align is_unit.op IsUnit.op
#align is_add_unit.op IsAddUnit.op

@[to_additive]
nonrec theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (Units.opEquiv u), rfl⟩
#align is_unit.unop IsUnit.unop
#align is_add_unit.unop IsAddUnit.unop

@[to_additive (attr := simp)]
theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m :=
  ⟨IsUnit.unop, IsUnit.op⟩
#align is_unit_op isUnit_op
#align is_add_unit_op isAddUnit_op

@[to_additive (attr := simp)]
theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m :=
  ⟨IsUnit.op, IsUnit.unop⟩
#align is_unit_unop isUnit_unop
#align is_add_unit_unop isAddUnit_unop

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
      "An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an
      additive semigroup homomorphism `AddHom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the
      (fully faithful)`ᵃᵒᵖ`-functor on morphisms."]
def MulHom.op {M N} [Mul M] [Mul N] : (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop,
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op,
      map_mul' := fun x y => congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align mul_hom.op MulHom.op
#align add_hom.op AddHom.op
#align mul_hom.op_symm_apply_apply MulHom.op_symm_apply_apply
#align mul_hom.op_apply_apply MulHom.op_apply_apply
#align add_hom.op_symm_apply_apply AddHom.op_symm_apply_apply
#align add_hom.op_apply_apply AddHom.op_apply_apply

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `MulHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse
      to `AddHom.op`."]
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm
#align mul_hom.unop MulHom.unop
#align add_hom.unop AddHom.unop

/-- An additive semigroup homomorphism `AddHom M N` can equivalently be viewed as an additive
homomorphism `AddHom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
def AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop,
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_hom.mul_op AddHom.mulOp
#align add_hom.mul_op_symm_apply_apply AddHom.mulOp_symm_apply_apply
#align add_hom.mul_op_apply_apply AddHom.mulOp_apply_apply

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddHom.mul_op`. -/
@[simp]
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm
#align add_hom.mul_unop AddHom.mulUnop

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive (attr := simps)
      "An additive monoid homomorphism `M →+ N` can equivalently be viewed as an
      additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)
      `ᵃᵒᵖ`-functor on morphisms."]
def MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, map_one' := congrArg MulOpposite.op f.map_one,
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, map_one' := congrArg unop f.map_one,
      map_mul' := fun x y => congrArg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align monoid_hom.op MonoidHom.op
#align add_monoid_hom.op AddMonoidHom.op
#align monoid_hom.op_apply_apply MonoidHom.op_apply_apply
#align monoid_hom.op_symm_apply_apply MonoidHom.op_symm_apply_apply
#align add_monoid_hom.op_apply_apply AddMonoidHom.op_apply_apply
#align add_monoid_hom.op_symm_apply_apply AddMonoidHom.op_symm_apply_apply

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `MonoidHom.op`. -/
@[to_additive (attr := simp)
      "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to
      `AddMonoidHom.op`."]
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm
#align monoid_hom.unop MonoidHom.unop
#align add_monoid_hom.unop AddMonoidHom.unop

/-- A monoid is isomorphic to the opposite of its opposite. -/
@[to_additive (attr := simps!)
      "A additive monoid is isomorphic to the opposite of its opposite."]
def MulEquiv.opOp (M : Type*) [Mul M] : M ≃* Mᵐᵒᵖᵐᵒᵖ where
  __ := MulOpposite.opEquiv.trans MulOpposite.opEquiv
  map_mul' _ _ := rfl

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ MulOpposite.unop, map_zero' := unop_injective f.map_zero,
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := MulOpposite.unop ∘ f ∘ MulOpposite.op,
      map_zero' := congrArg MulOpposite.unop f.map_zero,
      map_add' :=
        fun x y => congrArg MulOpposite.unop (f.map_add (MulOpposite.op x) (MulOpposite.op y)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align add_monoid_hom.mul_op AddMonoidHom.mulOp
#align add_monoid_hom.mul_op_symm_apply_apply AddMonoidHom.mulOp_symm_apply_apply
#align add_monoid_hom.mul_op_apply_apply AddMonoidHom.mulOp_apply_apply

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`AddMonoidHom.mul_op`. -/
@[simp]
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm
#align add_monoid_hom.mul_unop AddMonoidHom.mulUnop

/-- An iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)
  left_inv _ := rfl
  right_inv _ := rfl
#align add_equiv.mul_op AddEquiv.mulOp
#align add_equiv.mul_op_apply AddEquiv.mulOp_apply
#align add_equiv.mul_op_symm_apply AddEquiv.mulOp_symm_apply

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `AddEquiv.mul_op`. -/
@[simp]
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm
#align add_equiv.mul_unop AddEquiv.mulUnop

/-- An iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive (attr := simps)
  "An iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`."]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) where
  toFun f :=
    { toFun := MulOpposite.op ∘ f ∘ unop, invFun := MulOpposite.op ∘ f.symm ∘ unop,
      left_inv := fun x => unop_injective (f.symm_apply_apply x.unop),
      right_inv := fun x => unop_injective (f.apply_symm_apply x.unop),
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ MulOpposite.op, invFun := unop ∘ f.symm ∘ MulOpposite.op,
      left_inv := fun x => by simp,
      right_inv := fun x => by simp,
      map_mul' := fun x y => congr_arg unop (f.map_mul (MulOpposite.op y) (MulOpposite.op x)) }
  left_inv _ := rfl
  right_inv _ := rfl
#align mul_equiv.op MulEquiv.op
#align add_equiv.op AddEquiv.op
#align mul_equiv.op_symm_apply_symm_apply MulEquiv.op_symm_apply_symm_apply
#align mul_equiv.op_apply_apply MulEquiv.op_apply_apply
#align mul_equiv.op_apply_symm_apply MulEquiv.op_apply_symm_apply
#align mul_equiv.op_symm_apply_apply MulEquiv.op_symm_apply_apply
#align add_equiv.op_symm_apply_symm_apply AddEquiv.op_symm_apply_symm_apply
#align add_equiv.op_apply_apply AddEquiv.op_apply_apply
#align add_equiv.op_apply_symm_apply AddEquiv.op_apply_symm_apply
#align add_equiv.op_symm_apply_apply AddEquiv.op_symm_apply_apply

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `MulEquiv.op`. -/
@[to_additive (attr := simp)
  "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `AddEquiv.op`."]
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) :=
  MulEquiv.op.symm
#align mul_equiv.unop MulEquiv.unop
#align add_equiv.unop AddEquiv.unop

section Ext

/-- This ext lemma changes equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `Finsupp.addHom_ext'`. -/
@[ext]
theorem AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ →+ β)
    (h :
      f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g :=
  AddMonoidHom.ext <| MulOpposite.rec' fun x => (DFunLike.congr_fun h : _) x
#align add_monoid_hom.mul_op_ext AddMonoidHom.mul_op_ext

end Ext
