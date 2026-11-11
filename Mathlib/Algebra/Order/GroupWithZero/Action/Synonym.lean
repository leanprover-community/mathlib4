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

instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ᵒᵈ M₀ :=
  inferInstanceAs <| SMulZeroClass G₀ M₀

instance [Zero M₀] [SMulZeroClass G₀ M₀] : SMulZeroClass G₀ M₀ᵒᵈ :=
  inferInstanceAs <| SMulZeroClass G₀ M₀

instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ᵒᵈ M₀ :=
  inferInstanceAs <| SMulWithZero G₀ M₀

instance [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ M₀ᵒᵈ :=
  inferInstanceAs <| SMulWithZero G₀ M₀

instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ᵒᵈ M₀ :=
  inferInstanceAs <| DistribSMul G₀ M₀

instance [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ M₀ᵒᵈ :=
  inferInstanceAs <| DistribSMul G₀ M₀

instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ᵒᵈ M₀ :=
  inferInstanceAs <| DistribMulAction G₀ M₀

instance [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] : DistribMulAction G₀ M₀ᵒᵈ :=
  inferInstanceAs <| DistribMulAction G₀ M₀

instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ᵒᵈ M₀ := inferInstanceAs <| MulActionWithZero G₀ M₀

instance [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ M₀ᵒᵈ := inferInstanceAs <| MulActionWithZero G₀ M₀

end OrderDual

namespace Lex

instance instSMulWithZero [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero (Lex G₀) M₀ where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul ..

instance instSMulWithZero' [Zero G₀] [Zero M₀] [SMulWithZero G₀ M₀] : SMulWithZero G₀ (Lex M₀) where
  smul_zero _ := Lex.ext (smul_zero _)
  zero_smul _ := Lex.ext (zero_smul ..)

instance instDistribSMul [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul (Lex G₀) M₀ where
  smul_zero _ := smul_zero _
  smul_add _ _ _ := smul_add ..

instance instDistribSMul' [AddZeroClass M₀] [DistribSMul G₀ M₀] : DistribSMul G₀ (Lex M₀) where
  smul_zero _ := Lex.ext (smul_zero _)
  smul_add _ _ _ := Lex.ext (smul_add ..)

instance instDistribMulAction [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction (Lex G₀) M₀ where
  smul_zero := smul_zero
  smul_add := smul_add

instance instDistribMulAction' [Monoid G₀] [AddMonoid M₀] [DistribMulAction G₀ M₀] :
    DistribMulAction G₀ (Lex M₀) where
  smul_zero := smul_zero
  smul_add := smul_add

instance instMulActionWithZero [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero (Lex G₀) M₀ where
  smul_zero := smul_zero
  zero_smul := zero_smul _

instance instMulActionWithZero' [MonoidWithZero G₀] [AddMonoid M₀] [MulActionWithZero G₀ M₀] :
    MulActionWithZero G₀ (Lex M₀) where
  smul_zero := smul_zero
  zero_smul := zero_smul _

end Lex
