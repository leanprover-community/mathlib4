/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Faithful

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `Sum` type.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
-/

assert_not_exists MonoidWithZero

variable {M N α β : Type*}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α ⊕ β)

@[to_additive Sum.hasVAdd]
instance : SMul M (α ⊕ β) :=
  ⟨fun a => Sum.map (a • ·) (a • ·)⟩

@[to_additive]
theorem smul_def : a • x = x.map (a • ·) (a • ·) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_inl : a • (inl b : α ⊕ β) = inl (a • b) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_inr : a • (inr c : α ⊕ β) = inr (a • c) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl

instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α ⊕ β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α ⊕ β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α ⊕ β) :=
  ⟨fun a x => by
    cases x
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (α ⊕ β) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩

@[to_additive]
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (α ⊕ β) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] :
    MulAction M (α ⊕ β) where
  mul_smul a b x := by
    cases x
    exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by
    cases x
    exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum
