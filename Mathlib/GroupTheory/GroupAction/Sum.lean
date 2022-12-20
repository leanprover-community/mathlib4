/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.sum
! leanprover-community/mathlib commit f1a2caaf51ef593799107fe9a8d5e411599f3996
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `Sum` type.

## See also

* `GroupTheory.GroupAction.Option`
* `GroupTheory.GroupAction.Pi`
* `GroupTheory.GroupAction.Prod`
* `GroupTheory.GroupAction.Sigma`
-/


variable {M N P α β γ : Type _}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : Sum α β)

@[to_additive Sum.hasVadd]
instance : SMul M (Sum α β) :=
  ⟨fun a => Sum.map ((· • ·) a) ((· • ·) a)⟩

@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) ((· • ·) a) :=
  rfl
#align sum.smul_def Sum.smul_def

@[simp, to_additive]
theorem smul_inl : a • (inl b : Sum α β) = inl (a • b) :=
  rfl
#align sum.smul_inl Sum.smul_inl

@[simp, to_additive]
theorem smul_inr : a • (inr c : Sum α β) = inr (a • c) :=
  rfl
#align sum.smul_inr Sum.smul_inr

@[simp, to_additive]
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl
#align sum.smul_swap Sum.smul_swap

instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    exacts[congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    exacts[congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (Sum α β) :=
  ⟨fun a x => by
    cases x
    exacts[congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (Sum α β) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩
#align sum.has_faithful_smul_left Sum.FaithfulSMulLeft

@[to_additive]
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (Sum α β) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩
#align sum.has_faithful_smul_right Sum.FaithfulSMulRight

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] :
    MulAction M
      (Sum α
        β) where
  mul_smul a b x := by
    cases x
    exacts[congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by
    cases x
    exacts[congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum
