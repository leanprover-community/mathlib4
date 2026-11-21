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

public section

variable {M N α : Type*}

namespace OrderDual

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α := inferInstanceAs <| MulAction M α

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction M αᵒᵈ := inferInstanceAs <| MulAction M α

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α :=
  ‹SMulCommClass M N α›

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α :=
  ‹SMulCommClass M N α›

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ :=
  ‹SMulCommClass M N α›

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mᵒᵈ N α :=
  ‹IsScalarTower M N α›

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M Nᵒᵈ α :=
  ‹IsScalarTower M N α›

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵒᵈ :=
  ‹IsScalarTower M N α›

end OrderDual

namespace Lex

@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α where
  mul_smul _ _ _ := mul_smul ..
  one_smul _ := one_smul ..

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α) where
  mul_smul _ _ _ := Lex.ext (mul_smul ..)
  one_smul _ := Lex.ext (one_smul ..)

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass (Lex M) N α where smul_comm a := smul_comm a.ofLex

@[to_additive]
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M (Lex N) α where smul_comm _ a := smul_comm _ a.ofLex

@[to_additive]
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (Lex α) where smul_comm _ _ _ := Lex.ext (smul_comm ..)

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower (Lex M) N α where smul_assoc a := smul_assoc a.ofLex

@[to_additive]
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M (Lex N) α where smul_assoc _ a := smul_assoc _ a.ofLex

@[to_additive]
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N (Lex α) where smul_assoc _ _ _ := Lex.ext (smul_assoc ..)

end Lex
