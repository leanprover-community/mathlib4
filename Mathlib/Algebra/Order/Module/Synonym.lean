/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Action instances for `OrderDual`

This file provides instances of algebraic actions for `OrderDual`. Note that the `SMul` instances
are already defined in `Mathlib.Algebra.Order.Group.Synonym`.

## See also

* `Mathlib.Algebra.Order.Group.Synonym`
* `Mathlib.Algebra.Order.Ring.Synonym`
-/

namespace OrderDual
variable {α β γ : Type*}

instance instSMulWithZero [Zero α] [Zero β] [SMulWithZero α β] : SMulWithZero αᵒᵈ β where
  zero_smul := zero_smul α
  smul_zero := smul_zero (M := α)

instance instSMulWithZero' [Zero α] [Zero β] [SMulWithZero α β] : SMulWithZero α βᵒᵈ where
  zero_smul := zero_smul _ (M := β)
  smul_zero := smul_zero (A := β)

@[to_additive]
instance instMulAction [Monoid α] [MulAction α β] : MulAction αᵒᵈ β where
  one_smul := one_smul α
  mul_smul := mul_smul (α := α)

@[to_additive]
instance instMulAction' [Monoid α] [MulAction α β] : MulAction α βᵒᵈ where
  one_smul := one_smul _ (α := β)
  mul_smul := mul_smul (β := β)

@[to_additive]
instance instSMulCommClass [SMul β γ] [SMul α γ] [SMulCommClass α β γ] : SMulCommClass αᵒᵈ β γ :=
   ‹SMulCommClass α β γ›

@[to_additive]
instance instSMulCommClass' [SMul β γ] [SMul α γ] [SMulCommClass α β γ] : SMulCommClass α βᵒᵈ γ :=
  ‹SMulCommClass α β γ›

@[to_additive]
instance instSMulCommClass'' [SMul β γ] [SMul α γ] [SMulCommClass α β γ] : SMulCommClass α β γᵒᵈ :=
  ‹SMulCommClass α β γ›

@[to_additive instVAddAssocClass]
instance instIsScalarTower [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
   IsScalarTower αᵒᵈ β γ := ‹IsScalarTower α β γ›

@[to_additive instVAddAssocClass']
instance instIsScalarTower' [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
    IsScalarTower α βᵒᵈ γ := ‹IsScalarTower α β γ›

@[to_additive instVAddAssocClass'']
instance instIsScalarTower'' [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
    IsScalarTower α β γᵒᵈ := ‹IsScalarTower α β γ›

instance instMulActionWithZero [MonoidWithZero α] [AddMonoid β] [MulActionWithZero α β] :
    MulActionWithZero αᵒᵈ β :=
  { OrderDual.instMulAction, OrderDual.instSMulWithZero with }

instance instMulActionWithZero' [MonoidWithZero α] [AddMonoid β] [MulActionWithZero α β] :
    MulActionWithZero α βᵒᵈ :=
  { OrderDual.instMulAction', OrderDual.instSMulWithZero' with }

instance instDistribMulAction [MonoidWithZero α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction αᵒᵈ β where
  smul_add := smul_add (M := α)
  smul_zero := smul_zero (M := α)

instance instDistribMulAction' [MonoidWithZero α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α βᵒᵈ where
  smul_add := smul_add (A := β)
  smul_zero := smul_zero (A := β)

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul := add_smul (R := α)
  zero_smul := zero_smul _

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ where
  add_smul := add_smul (M := β)
  zero_smul := zero_smul _

end OrderDual
