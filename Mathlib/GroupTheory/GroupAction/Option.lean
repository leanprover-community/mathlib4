/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Option instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on `option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


variable {M N α : Type _}

namespace Option

section HasSmul

variable [HasSmul M α] [HasSmul N α] (a : M) (b : α) (x : Option α)

@[to_additive Option.hasVadd]
instance : HasSmul M (Option α) :=
  ⟨fun a => Option.map <| (· • ·) a⟩

@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) :=
  rfl
#align option.smul_def Option.smul_def

@[simp, to_additive]
theorem smul_none : a • (none : Option α) = none :=
  rfl
#align option.smul_none Option.smul_none

@[simp, to_additive]
theorem smul_some : a • some b = some (a • b) :=
  rfl
#align option.smul_some Option.smul_some

@[to_additive]
instance [HasSmul M N] [IsScalarTower M N α] : IsScalarTower M N (Option α) :=
  ⟨fun a b x => by
    cases x
    exacts[rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SmulCommClass M N α] : SmulCommClass M N (Option α) :=
  ⟨fun a b => Function.Commute.option_map <| smul_comm _ _⟩

@[to_additive]
instance [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α) :=
  ⟨fun a x => by
    cases x
    exacts[rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]
instance [HasFaithfulSmul M α] : HasFaithfulSmul M (Option α) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

end HasSmul

instance [Monoid M] [MulAction M α] :
    MulAction M (Option α) where
  smul := (· • ·)
  one_smul b := by
    cases b
    exacts[rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts[rfl, congr_arg some (mul_smul _ _ _)]

end Option
