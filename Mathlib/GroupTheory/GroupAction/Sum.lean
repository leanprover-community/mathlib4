/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.sum from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `Sum` type.

## See also

* `GroupTheory.GroupAction.Option`
* `GroupTheory.GroupAction.Pi`
* `GroupTheory.GroupAction.Prod`
* `GroupTheory.GroupAction.Sigma`
-/


variable {M N P α β γ : Type*}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : Sum α β)

@[to_additive Sum.hasVAdd]
instance : SMul M (Sum α β) :=
  ⟨fun a => Sum.map ((· • ·) a) ((· • ·) a)⟩

@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) ((· • ·) a) :=
  rfl
#align sum.smul_def Sum.smul_def
#align sum.vadd_def Sum.vadd_def

@[to_additive (attr := simp)]
theorem smul_inl : a • (inl b : Sum α β) = inl (a • b) :=
  rfl
#align sum.smul_inl Sum.smul_inl
#align sum.vadd_inl Sum.vadd_inl

@[to_additive (attr := simp)]
theorem smul_inr : a • (inr c : Sum α β) = inr (a • c) :=
  rfl
#align sum.smul_inr Sum.smul_inr
#align sum.vadd_inr Sum.vadd_inr

@[to_additive (attr := simp)]
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl
                                                    -- ⊢ swap (a • inl val✝) = a • swap (inl val✝)
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align sum.smul_swap Sum.smul_swap
#align sum.vadd_swap Sum.vadd_swap

instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    -- ⊢ (a • b) • inl val✝ = a • b • inl val✝
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩
    -- 🎉 no goals

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    -- ⊢ a • b • inl val✝ = b • a • inl val✝
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩
    -- 🎉 no goals

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (Sum α β) :=
  ⟨fun a x => by
    cases x
    -- ⊢ MulOpposite.op a • inl val✝ = a • inl val✝
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩
    -- 🎉 no goals

@[to_additive]
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (Sum α β) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩
                                               -- 🎉 no goals
#align sum.has_faithful_smul_left Sum.FaithfulSMulLeft
#align sum.has_faithful_vadd_left Sum.FaithfulVAddLeft

@[to_additive]
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (Sum α β) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩
                                               -- 🎉 no goals
#align sum.has_faithful_smul_right Sum.FaithfulSMulRight
#align sum.has_faithful_vadd_right Sum.FaithfulVAddRight

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] :
    MulAction M
      (Sum α
        β) where
  mul_smul a b x := by
    cases x
    -- ⊢ (a * b) • inl val✝ = a • b • inl val✝
    exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
    -- 🎉 no goals
    -- ⊢ 1 • inl val✝ = inl val✝
  one_smul x := by
    -- 🎉 no goals
    cases x
    exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum
