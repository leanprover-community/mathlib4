/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.opposite from "leanprover-community/mathlib"@"4330aae21f538b862f8aead371cfb6ee556398f1"

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `SMul R Mᵐᵒᵖ`, and actions by the opposite
type, `SMul Rᵐᵒᵖ M`.

Note that `MulOpposite.smul` is provided in an earlier file as it is needed to
provide the `AddMonoid.nsmul` and `AddCommGroup.zsmul` fields.

## Notation

With `open scoped RightActions`, this provides:

* `r •> m` as an alias for `r • m`
* `m <• r` as an alias for `MulOpposite.op r • m`
* `v +ᵥ> p` as an alias for `v +ᵥ p`
* `p <+ᵥ v` as an alias for `AddOpposite.op v +ᵥ p`
-/


variable (α : Type*)

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/


namespace MulOpposite

@[to_additive]
instance mulAction (R : Type*) [Monoid R] [MulAction R α] : MulAction R αᵐᵒᵖ :=
  { one_smul := fun x => unop_injective <| one_smul R (unop x)
    mul_smul := fun r₁ r₂ x => unop_injective <| mul_smul r₁ r₂ (unop x) }

instance distribMulAction (R : Type*) [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R αᵐᵒᵖ :=
  { smul_add := fun r x₁ x₂ => unop_injective <| smul_add r (unop x₁) (unop x₂)
    smul_zero := fun r => unop_injective <| smul_zero r }

instance mulDistribMulAction (R : Type*) [Monoid R] [Monoid α] [MulDistribMulAction R α] :
    MulDistribMulAction R αᵐᵒᵖ :=
  { smul_mul := fun r x₁ x₂ => unop_injective <| smul_mul' r (unop x₂) (unop x₁)
    smul_one := fun r => unop_injective <| smul_one r }

@[to_additive]
instance isScalarTower {M N} [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵐᵒᵖ :=
  ⟨fun _ _ _ => unop_injective <| smul_assoc _ _ _⟩

@[to_additive]
instance smulCommClass {M N} [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵐᵒᵖ :=
  ⟨fun _ _ _ => unop_injective <| smul_comm _ _ _⟩

@[to_additive]
instance isCentralScalar (R : Type*) [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] :
    IsCentralScalar R αᵐᵒᵖ :=
  ⟨fun _ _ => unop_injective <| op_smul_eq_smul _ _⟩

theorem op_smul_eq_op_smul_op {R : Type*} [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α]
    (r : R) (a : α) : op (r • a) = op r • op a :=
  (op_smul_eq_smul r (op a)).symm
#align mul_opposite.op_smul_eq_op_smul_op MulOpposite.op_smul_eq_op_smul_op

theorem unop_smul_eq_unop_smul_unop {R : Type*} [SMul R α] [SMul Rᵐᵒᵖ α]
    [IsCentralScalar R α] (r : Rᵐᵒᵖ) (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a :=
  (unop_smul_eq_smul r (unop a)).symm
#align mul_opposite.unop_smul_eq_unop_smul_unop MulOpposite.unop_smul_eq_unop_smul_unop

end MulOpposite

/-! ### Right actions

In this section we establish `SMul αᵐᵒᵖ β` as the canonical spelling of right scalar multiplication
of `β` by `α`, and provide convenient notations.
-/

namespace RightActions

/-- With `open scoped RightActions`, an alternative symbol for left actions, `r • m`.

In lemma names this is still called `smul`. -/
scoped notation3:74 r:75 " •> " m:74 => r • m

/-- With `open scoped RightActions`, a shorthand for right actions, `op r • m`.

In lemma names this is still called `op_smul`. -/
scoped notation3:73 m:73 " <• " r:74 => MulOpposite.op r • m

/-- With `open scoped RightActions`, an alternative symbol for left actions, `r • m`.

In lemma names this is still called `vadd`. -/
scoped notation3:74 r:75 " +ᵥ> " m:74 => r +ᵥ m

/-- With `open scoped RightActions`, a shorthand for right actions, `op r +ᵥ m`.

In lemma names this is still called `op_vadd`. -/
scoped notation3:73 m:73 " <+ᵥ " r:74 => AddOpposite.op r +ᵥ m

section examples
variable {α β : Type*} [SMul α β] [SMul αᵐᵒᵖ β] [VAdd α β] [VAdd αᵃᵒᵖ β] {a a₁ a₂ a₃ a₄ : α} {b : β}

-- Left and right actions are just notation around the general `•` and `+ᵥ` notations
example : a •> b = a • b := rfl
example : b <• a = MulOpposite.op a • b := rfl

example : a +ᵥ> b = a +ᵥ b := rfl
example : b <+ᵥ a = AddOpposite.op a +ᵥ b := rfl

-- Left actions right-associate, right actions left-associate
example : a₁ •> a₂ •> b = a₁ •> (a₂ •> b) := rfl
example : b <• a₂ <• a₁ = (b <• a₂) <• a₁ := rfl

example : a₁ +ᵥ> a₂ +ᵥ> b = a₁ +ᵥ> (a₂ +ᵥ> b) := rfl
example : b <+ᵥ a₂ <+ᵥ a₁ = (b <+ᵥ a₂) <+ᵥ a₁ := rfl

-- When left and right actions coexist, they associate to the left
example : a₁ •> b <• a₂ = (a₁ •> b) <• a₂ := rfl
example : a₁ •> a₂ •> b <• a₃ <• a₄ = ((a₁ •> (a₂ •> b)) <• a₃) <• a₄ := rfl

example : a₁ +ᵥ> b <+ᵥ a₂ = (a₁ +ᵥ> b) <+ᵥ a₂ := rfl
example : a₁ +ᵥ> a₂ +ᵥ> b <+ᵥ a₃ <+ᵥ a₄ = ((a₁ +ᵥ> (a₂ +ᵥ> b)) <+ᵥ a₃) <+ᵥ a₄ := rfl

end examples

end RightActions

section
variable {α β : Type*}

open scoped RightActions

@[to_additive]
theorem op_smul_op_smul [Monoid α] [MulAction αᵐᵒᵖ β] (b : β) (a₁ a₂ : α) :
    b <• a₁ <• a₂ = b <• (a₁ * a₂) := smul_smul _ _ _

@[to_additive]
theorem op_smul_mul [Monoid α] [MulAction αᵐᵒᵖ β] (b : β) (a₁ a₂ : α) :
    b <• (a₁ * a₂) = b <• a₁ <• a₂ := mul_smul _ _ _

end section

/-! ### Actions _by_ the opposite type (right actions)

In `Mul.toSMul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `MulOpposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/

open MulOpposite

/-- Like `Mul.toSMul`, but multiplies on the right.

See also `Monoid.toOppositeMulAction` and `MonoidWithZero.toOppositeMulActionWithZero`. -/
@[to_additive "Like `Add.toVAdd`, but adds on the right.

  See also `AddMonoid.to_OppositeAddAction`."]
instance Mul.toHasOppositeSMul [Mul α] : SMul αᵐᵒᵖ α :=
  ⟨fun c x => x * c.unop⟩
#align has_mul.to_has_opposite_smul Mul.toHasOppositeSMul
#align has_add.to_has_opposite_vadd Add.toHasOppositeVAdd

@[to_additive]
theorem op_smul_eq_mul [Mul α] {a a' : α} : op a • a' = a' * a :=
  rfl
#align op_smul_eq_mul op_smul_eq_mul
#align op_vadd_eq_add op_vadd_eq_add

@[to_additive (attr := simp)]
theorem MulOpposite.smul_eq_mul_unop [Mul α] {a : αᵐᵒᵖ} {a' : α} : a • a' = a' * a.unop :=
  rfl
#align mul_opposite.smul_eq_mul_unop MulOpposite.smul_eq_mul_unop
#align add_opposite.vadd_eq_add_unop AddOpposite.vadd_eq_add_unop

/-- The right regular action of a group on itself is transitive. -/
@[to_additive "The right regular action of an additive group on itself is transitive."]
instance MulAction.OppositeRegular.isPretransitive {G : Type*} [Group G] :
    MulAction.IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y => ⟨op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩
#align mul_action.opposite_regular.is_pretransitive MulAction.OppositeRegular.isPretransitive
#align add_action.opposite_regular.is_pretransitive AddAction.OppositeRegular.isPretransitive

@[to_additive]
instance Semigroup.opposite_smulCommClass [Semigroup α] :
    SMulCommClass αᵐᵒᵖ α α where smul_comm _ _ _ := mul_assoc _ _ _
#align semigroup.opposite_smul_comm_class Semigroup.opposite_smulCommClass
#align add_semigroup.opposite_vadd_comm_class AddSemigroup.opposite_vaddCommClass

@[to_additive]
instance Semigroup.opposite_smulCommClass' [Semigroup α] : SMulCommClass α αᵐᵒᵖ α :=
  SMulCommClass.symm _ _ _
#align semigroup.opposite_smul_comm_class' Semigroup.opposite_smulCommClass'
#align add_semigroup.opposite_vadd_comm_class' AddSemigroup.opposite_vaddCommClass'

@[to_additive]
instance CommSemigroup.isCentralScalar [CommSemigroup α] : IsCentralScalar α α :=
  ⟨fun _ _ => mul_comm _ _⟩
#align comm_semigroup.is_central_scalar CommSemigroup.isCentralScalar
#align add_comm_semigroup.is_central_scalar AddCommSemigroup.isCentralVAdd

/-- Like `Monoid.toMulAction`, but multiplies on the right. -/
@[to_additive "Like `AddMonoid.toAddAction`, but adds on the right."]
instance Monoid.toOppositeMulAction [Monoid α] :
    MulAction αᵐᵒᵖ α where
  smul := (· • ·)
  one_smul := mul_one
  mul_smul _ _ _ := (mul_assoc _ _ _).symm
#align monoid.to_opposite_mul_action Monoid.toOppositeMulAction
#align add_monoid.to_opposite_add_action AddMonoid.toOppositeAddAction

@[to_additive]
instance IsScalarTower.opposite_mid {M N} [Mul N] [SMul M N] [SMulCommClass M N N] :
    IsScalarTower M Nᵐᵒᵖ N :=
  ⟨fun _ _ _ => mul_smul_comm _ _ _⟩
#align is_scalar_tower.opposite_mid IsScalarTower.opposite_mid
#align vadd_assoc_class.opposite_mid VAddAssocClass.opposite_mid

@[to_additive]
instance SMulCommClass.opposite_mid {M N} [Mul N] [SMul M N] [IsScalarTower M N N] :
    SMulCommClass M Nᵐᵒᵖ N :=
  ⟨fun x y z => by
    induction y using MulOpposite.rec'
    simp only [smul_mul_assoc, MulOpposite.smul_eq_mul_unop]⟩
#align smul_comm_class.opposite_mid SMulCommClass.opposite_mid
#align vadd_comm_class.opposite_mid VAddCommClass.opposite_mid

-- The above instance does not create an unwanted diamond, the two paths to
-- `MulAction αᵐᵒᵖ αᵐᵒᵖ` are defeq.
example [Monoid α] : Monoid.toMulAction αᵐᵒᵖ = MulOpposite.mulAction α αᵐᵒᵖ :=
  rfl

/-- `Monoid.toOppositeMulAction` is faithful on cancellative monoids. -/
@[to_additive "`AddMonoid.toOppositeAddAction` is faithful on cancellative monoids."]
instance LeftCancelMonoid.toFaithfulSMul_opposite [LeftCancelMonoid α] :
    FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun h => unop_injective <| mul_left_cancel (h 1)⟩
#align left_cancel_monoid.to_has_faithful_opposite_scalar LeftCancelMonoid.toFaithfulSMul_opposite
#align add_left_cancel_monoid.to_has_faithful_opposite_scalar AddLeftCancelMonoid.toFaithfulVAdd_opposite

/-- `Monoid.toOppositeMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.toFaithfulSMul_opposite [CancelMonoidWithZero α]
    [Nontrivial α] : FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun h => unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_opposite_scalar CancelMonoidWithZero.toFaithfulSMul_opposite
