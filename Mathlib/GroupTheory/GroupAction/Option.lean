/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Defs

#align_import group_theory.group_action.option from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-!
# Option instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on `Option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `GroupTheory.GroupAction.Pi`
* `GroupTheory.GroupAction.Prod`
* `GroupTheory.GroupAction.Sigma`
* `GroupTheory.GroupAction.Sum`
-/


variable {M N α : Type*}

namespace Option

section SMul

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

@[to_additive Option.VAdd]
instance : SMul M (Option α) :=
  ⟨fun a => Option.map <| (a • ·)⟩

@[to_additive]
theorem smul_def : a • x = x.map (a • ·) :=
  rfl
#align option.smul_def Option.smul_def
#align option.vadd_def Option.vadd_def

@[to_additive (attr := simp)]
theorem smul_none : a • (none : Option α) = none :=
  rfl
#align option.smul_none Option.smul_none
#align option.vadd_none Option.vadd_none

@[to_additive (attr := simp)]
theorem smul_some : a • some b = some (a • b) :=
  rfl
#align option.smul_some Option.smul_some
#align option.vadd_some Option.vadd_some

@[to_additive]
instance instIsScalarTowerOfSMul [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (Option α) :=
  ⟨fun a b x => by
    cases x
    exacts [rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] : SMulCommClass M N (Option α) :=
  ⟨fun _ _ => Function.Commute.option_map <| smul_comm _ _⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α) :=
  ⟨fun a x => by
    cases x
    exacts [rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]
instance [FaithfulSMul M α] : FaithfulSMul M (Option α) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

end SMul

instance [Monoid M] [MulAction M α] :
    MulAction M (Option α) where
  smul := (· • ·)
  one_smul b := by
    cases b
    exacts [rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts [rfl, congr_arg some (mul_smul _ _ _)]

end Option
