/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Group.Synonym

/-!
# Actions by and on order synonyms

This PR transfers group action instances from a type `α` to `αᵒᵈ` and `Lex α`.

## See also

* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

variable {M N α : Type*}

namespace OrderDual

@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α := ‹MulAction M α›

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M αᵒᵈ := ‹MulAction M α›

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α :=
  ‹SMulCommClass M N α›

@[to_additive]
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α :=
  ‹SMulCommClass M N α›

@[to_additive]
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ :=
  ‹SMulCommClass M N α›

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower Mᵒᵈ N α := ‹IsScalarTower M N α›

@[to_additive]
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M Nᵒᵈ α := ‹IsScalarTower M N α›

@[to_additive]
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N αᵒᵈ := ‹IsScalarTower M N α›

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
