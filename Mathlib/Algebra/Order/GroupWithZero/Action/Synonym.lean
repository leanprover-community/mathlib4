/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Action.Synonym
public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Tactic.Common

/-!
# Actions by and on order synonyms

This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

public section

variable {G₀ M₀ : Type*}

namespace OrderDual

instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀ where
  smul_zero _ := by rw [← ofDual_smul', smul_zero]

instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ where
  smul_zero _ := by rw [← toDual_smul, ofDual_zero, smul_zero]; rfl

instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ where
  zero_smul _ := by rw [← toDual_zero, toDual_smul', zero_smul]

instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ where
  zero_smul _ := by rw [← toDual_smul, zero_smul]; rfl

instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ where
  smul_add _ _ _ := by rw [← ofDual_smul', smul_add]; rfl

instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ where
  smul_add _ _ _ := by rw [← toDual_smul, ofDual_add, smul_add]; rfl

instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀ where
  smul_zero _ := by rw [← ofDual_smul', smul_zero]
  smul_add _ _ _ := by rw [← ofDual_smul', smul_add]; rfl

instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ where
  smul_zero _ := by rw [← toDual_smul, ofDual_zero, smul_zero]; rfl
  smul_add _ _ _ := by rw [← toDual_smul, ofDual_add, smul_add]; rfl

instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ where
  smul_zero _ := by rw [← ofDual_smul', smul_zero]
  zero_smul _ := by rw [← toDual_zero, toDual_smul', zero_smul]

instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ where
  smul_zero _ := by rw [← toDual_smul, ofDual_zero, smul_zero]; rfl
  zero_smul _ := by rw [← toDual_smul, zero_smul]; rfl

end OrderDual

namespace Lex

instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ :=
  inferInstanceAs <| SMulWithZero G₀ M₀

instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) :=
  inferInstanceAs <| SMulWithZero G₀ M₀

instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ :=
  inferInstanceAs <| DistribSMul G₀ M₀

instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) :=
  inferInstanceAs <| DistribSMul G₀ M₀

instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction (Lex G₀) M₀ := inferInstanceAs <| DistribMulAction G₀ M₀

instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ (Lex M₀) := inferInstanceAs <| DistribMulAction G₀ M₀

instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero (Lex G₀) M₀ := inferInstanceAs <| MulActionWithZero G₀ M₀

instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ (Lex M₀) := inferInstanceAs <| MulActionWithZero G₀ M₀

end Lex
