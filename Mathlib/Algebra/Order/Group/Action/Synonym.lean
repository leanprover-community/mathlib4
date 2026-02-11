/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Actions by and on order synonyms

This PR transfers group action instances from a type `α` to `αᵒᵈ` and `Lex α`.

## See also

* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

@[expose] public section

open OrderDual

variable {M N α : Type*}

namespace OrderDual

@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α where
  one_smul := one_smul M
  mul_smul x y := mul_smul (ofDual x) (ofDual y)

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M αᵒᵈ :=
  ofDual_injective.mulAction ofDual (fun _ _ => rfl)

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass Mᵒᵈ N α where
  smul_comm m := smul_comm (ofDual m)

@[to_additive]
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M Nᵒᵈ α where
  smul_comm m n := smul_comm m (ofDual n)

@[to_additive]
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N αᵒᵈ where
  smul_comm m n a := ext (smul_comm m n (ofDual a))

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵒᵈ N α where
  smul_assoc x y := smul_assoc (ofDual x) y

@[to_additive]
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M Nᵒᵈ α where
  smul_assoc x y := smul_assoc x (ofDual y)

@[to_additive]
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵒᵈ where
  smul_assoc x y z := ext (smul_assoc x y (ofDual z))

end OrderDual

namespace Lex

@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α := ‹MulAction M α›

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α) := ‹MulAction M α›

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass (Lex M) N α := ‹SMulCommClass M N α›

@[to_additive]
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M (Lex N) α := ‹SMulCommClass M N α›

@[to_additive]
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (Lex α) := ‹SMulCommClass M N α›

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower (Lex M) N α := ‹IsScalarTower M N α›

@[to_additive]
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M (Lex N) α := ‹IsScalarTower M N α›

@[to_additive]
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N (Lex α) := ‹IsScalarTower M N α›

end Lex
