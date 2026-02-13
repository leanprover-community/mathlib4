/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
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

@[expose] public section

open OrderDual

variable {G₀ M₀ : Type*}

namespace OrderDual

instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ where
  smul_zero a := smul_zero (ofDual a)
  zero_smul := zero_smul G₀

instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ :=
  ofDual_injective.smulWithZero ⟨ofDual, rfl⟩ (fun _ _ => rfl)

instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ where
  smul_zero a := smul_zero (ofDual a)
  smul_add a := smul_add (ofDual a)

instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ :=
  ofDual_injective.distribSMul
    { toFun := ofDual, map_zero' := rfl, map_add' := fun _ _ => rfl } (fun _ _ => rfl)

instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ᵒᵈ M₀ where
  one_smul := one_smul G₀
  mul_smul x y := mul_smul (ofDual x) (ofDual y)
  smul_zero a := smul_zero (ofDual a)
  smul_add a := smul_add (ofDual a)

instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ M₀ᵒᵈ :=
  ofDual_injective.distribMulAction
    { toFun := ofDual, map_zero' := rfl, map_add' := fun _ _ => rfl } (fun _ _ => rfl)

instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ where
  one_smul := one_smul G₀
  mul_smul x y := mul_smul (ofDual x) (ofDual y)
  smul_zero a := smul_zero (ofDual a)
  zero_smul := zero_smul G₀

instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ :=
  ofDual_injective.mulActionWithZero ⟨ofDual, rfl⟩ (fun _ _ => rfl)

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
