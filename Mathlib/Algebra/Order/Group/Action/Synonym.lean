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
instance [Monoid M] [MulAction M α] : MulAction Mᵒᵈ α where
  mul_smul _ _ _ := by rw [← ofDual_smul', ofDual_mul, mul_smul]; rfl
  one_smul _ := by rw [← toDual_one, ← ofDual_smul', one_smul]

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction M αᵒᵈ where
  mul_smul _ _ _ := by rw [← toDual_smul, mul_smul]; rfl
  one_smul _ := by rw [← toDual_smul, one_smul]

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass Mᵒᵈ N α where
  smul_comm _ _ _ := by rw [← ofDual_smul', smul_comm]; rfl

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M Nᵒᵈ α where
  smul_comm _ _ _ := by rw [← ofDual_smul', smul_comm]; rfl

@[to_additive]
instance [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵒᵈ where
  smul_comm _ _ _ := by rw [← toDual_smul, ofDual_smul, smul_comm]; rfl

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower Mᵒᵈ N α where
  smul_assoc _ _ _ := by rw [← ofDual_smul', smul_assoc, ofDual_smul']

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M Nᵒᵈ α where
  smul_assoc _ _ _ := by rw [← ofDual_smul', ofDual_smul, smul_assoc]; rfl

@[to_additive]
instance [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵒᵈ where
  smul_assoc _ _ _ := by rw [← toDual_smul, smul_assoc]; rfl

end OrderDual

namespace Lex

@[to_additive]
instance instMulAction [Monoid M] [MulAction M α] : MulAction (Lex M) α :=
  inferInstanceAs <| MulAction M α

@[to_additive]
instance instMulAction' [Monoid M] [MulAction M α] : MulAction M (Lex α) :=
  inferInstanceAs <| MulAction M α

@[to_additive]
instance instSMulCommClass [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass (Lex M) N α := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
instance instSMulCommClass' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M (Lex N) α := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
instance instSMulCommClass'' [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (Lex α) := inferInstanceAs <| SMulCommClass M N α

@[to_additive]
instance instIsScalarTower [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower (Lex M) N α := inferInstanceAs <| IsScalarTower M N α

@[to_additive]
instance instIsScalarTower' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M (Lex N) α := inferInstanceAs <| IsScalarTower M N α

@[to_additive]
instance instIsScalarTower'' [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] :
    IsScalarTower M N (Lex α) := inferInstanceAs <| IsScalarTower M N α

end Lex
