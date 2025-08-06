/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.GroupWithZero.Synonym
import Mathlib.Tactic.Common

/-!
# Actions by and on order synonyms

This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/Module/Synonym.lean`
-/

variable {G₀ M₀ : Type*}

namespace OrderDual

instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ where
  smul_zero _ := smul_zero (M := G₀) _
  zero_smul := zero_smul (M₀ := G₀)

instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ where
  smul_zero _ := congrArg toDual (smul_zero _)
  zero_smul _ := congrArg toDual (zero_smul _ _)

instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ where
  smul_zero _ := smul_zero (M := G₀) _
  smul_add a := smul_add a.ofDual

instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ where
  smul_zero _ := congrArg toDual (smul_zero _)
  smul_add _ _ _ := congrArg toDual (smul_add _ _ _)

instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ᵒᵈ M₀ where
  __ : DistribSMul G₀ᵒᵈ M₀ := inferInstance
  one_smul := one_smul (M := G₀)
  mul_smul _ _ := mul_smul (α := G₀) _ _


instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ M₀ᵒᵈ where
  __ : DistribSMul G₀ M₀ᵒᵈ := inferInstance
  one_smul _ := congrArg toDual (one_smul _ _)
  mul_smul _ _ _ := congrArg toDual (mul_smul _ _ _)

instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ where
  __ : SMulWithZero G₀ᵒᵈ M₀ := inferInstance
  one_smul := one_smul (M := G₀)
  mul_smul _ _ := mul_smul (α := G₀) _ _

instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ where
  __ : SMulWithZero G₀ M₀ᵒᵈ := inferInstance
  one_smul _ := congrArg toDual (one_smul _ _)
  mul_smul _ _ _ := congrArg toDual (mul_smul _ _ _)

end OrderDual

namespace Lex

instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ :=
  ‹SMulWithZero G₀ M₀›

instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) :=
  ‹SMulWithZero G₀ M₀›

instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ :=
  ‹DistribSMul G₀ M₀›

instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) :=
  ‹DistribSMul G₀ M₀›

instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction (Lex G₀) M₀ := ‹DistribMulAction G₀ M₀›

instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ (Lex M₀) := ‹DistribMulAction G₀ M₀›

instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero (Lex G₀) M₀ := ‹MulActionWithZero G₀ M₀›

instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ (Lex M₀) := ‹MulActionWithZero G₀ M₀›

end Lex
