/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Order.Group.Synonym

/-!
# Group with zero structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/

@[expose] public section


open Function

variable {α : Type*}


/-! ### Order dual -/


open OrderDual

instance [MulZeroClass α] : MulZeroClass αᵒᵈ :=
  ofDual_injective.mulZeroClass ofDual rfl fun _ _ => rfl

instance [MulZeroOneClass α] : MulZeroOneClass αᵒᵈ :=
  ofDual_injective.mulZeroOneClass ofDual rfl rfl fun _ _ => rfl

instance [Mul α] [Zero α] [NoZeroDivisors α] : NoZeroDivisors αᵒᵈ :=
  ofDual_injective.noZeroDivisors ofDual rfl fun _ _ => rfl

instance [SemigroupWithZero α] : SemigroupWithZero αᵒᵈ :=
  ofDual_injective.semigroupWithZero ofDual rfl fun _ _ => rfl

instance [MonoidWithZero α] : MonoidWithZero αᵒᵈ :=
  ofDual_injective.monoidWithZero ofDual rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsLeftCancelMulZero αᵒᵈ :=
  ofDual_injective.isLeftCancelMulZero ofDual rfl fun _ _ => rfl
instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsRightCancelMulZero αᵒᵈ :=
  ofDual_injective.isRightCancelMulZero ofDual rfl fun _ _ => rfl
instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵒᵈ :=
  ofDual_injective.isCancelMulZero ofDual rfl fun _ _ => rfl

instance [CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ :=
  ofDual_injective.commMonoidWithZero ofDual rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance [GroupWithZero α] : GroupWithZero αᵒᵈ :=
  ofDual_injective.groupWithZero ofDual rfl rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [CommGroupWithZero α] : CommGroupWithZero αᵒᵈ :=
  ofDual_injective.commGroupWithZero ofDual rfl rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-! ### Lexicographic order -/


instance [h : MulZeroClass α] : MulZeroClass (Lex α) := h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) := h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) := h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) := h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) := h

instance [Mul α] [Zero α] [h : IsLeftCancelMulZero α] : IsLeftCancelMulZero (Lex α) := h
instance [Mul α] [Zero α] [h : IsRightCancelMulZero α] : IsRightCancelMulZero (Lex α) := h
instance [Mul α] [Zero α] [h : IsCancelMulZero α] : IsCancelMulZero (Lex α) := h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) := h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) := h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) := h
