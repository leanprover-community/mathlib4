/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Action.Synonym
public import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Action instances for `OrderDual`


This PR transfers group action with zero instances from a type `α` to `αᵒᵈ` and `Lex α`. Note that
the `SMul` instances are already defined in `Mathlib/Algebra/Order/Group/Synonym.lean`.

## See also

* `Mathlib/Algebra/Order/Group/Action/Synonym.lean`
* `Mathlib/Algebra/Order/GroupWithZero/Action/Synonym.lean`
-/

@[expose] public section

variable {α β : Type*}

namespace OrderDual

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ β where
  add_smul r s := add_smul (ofDual r) (ofDual s)
  zero_smul := zero_smul α

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α βᵒᵈ :=
  Function.Injective.module _
    (⟨⟨ofDual, rfl⟩, fun _ _ => rfl⟩ : βᵒᵈ →+ β) ofDual_injective (fun _ _ => rfl)

end OrderDual

namespace Lex

instance instModule [Semiring α] [AddCommMonoid β] [Module α β] : Module (Lex α) β :=
  ‹Module α β›

instance instModule' [Semiring α] [AddCommMonoid β] [Module α β] : Module α (Lex β) :=
  ‹Module α β›

end Lex
