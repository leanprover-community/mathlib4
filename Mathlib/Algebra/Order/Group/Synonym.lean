/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Synonym

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/


@[to_additive]
instance [h : One α] : One αᵒᵈ := ⟨toDual 1⟩

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ := ⟨fun a b => toDual (a.ofDual * b.ofDual)⟩

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ := ⟨fun a => toDual a.ofDual⁻¹⟩

@[to_additive]
instance [h : Div α] : Div αᵒᵈ := ⟨fun a b => toDual (a.ofDual / b.ofDual)⟩

@[to_additive]
instance OrderDual.instSMul [SMul α β] : SMul α βᵒᵈ :=
  ⟨fun a b => toDual (a • b.ofDual)⟩

@[to_additive existing (reorder := 1 2) OrderDual.instSMul]
instance OrderDual.instPow [Pow α β] : Pow αᵒᵈ β :=
  ⟨fun a b => toDual (a.ofDual ^ b)⟩

@[to_additive]
instance OrderDual.instSMul' [SMul α β] : SMul αᵒᵈ β :=
  ⟨fun a b => (a.ofDual' • b)⟩

@[to_additive existing (reorder := 1 2) OrderDual.instSMul']
instance OrderDual.instPow' [h : Pow α β] : Pow α βᵒᵈ :=
  ⟨fun a b => (a ^ b.ofDual)⟩

@[to_additive]
instance [Semigroup α] : Semigroup αᵒᵈ where
  mul_assoc _ _ _ := congrArg toDual <| mul_assoc ..

@[to_additive]
instance [CommSemigroup α] : CommSemigroup αᵒᵈ where
  mul_comm _ _ := congrArg toDual <| mul_comm ..

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ where
  mul_left_cancel _ _ _ h := (congrArg toDual <| mul_left_cancel <| congrArg ofDual h)

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ where
  mul_right_cancel _ _ _ h := (congrArg toDual <| mul_right_cancel <| congrArg ofDual h)

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul αᵒᵈ where

@[to_additive]
instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ where
  __ := inferInstanceAs (IsLeftCancelMul αᵒᵈ)

@[to_additive]
instance [RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ where
  __ := inferInstanceAs (IsRightCancelMul αᵒᵈ)

@[to_additive]
instance [MulOneClass α] : MulOneClass αᵒᵈ where
  one_mul _ := congrArg toDual (one_mul _)
  mul_one _ := congrArg toDual (mul_one _)

@[to_additive]
instance [Monoid α] : Monoid αᵒᵈ where

@[to_additive]
instance OrderDual.instCommMonoid [CommMonoid α] : CommMonoid αᵒᵈ where

@[to_additive]
instance [LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ where

@[to_additive]
instance [RightCancelMonoid α] : RightCancelMonoid αᵒᵈ where

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵒᵈ where

@[to_additive]
instance OrderDual.instCancelCommMonoid [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ where

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv αᵒᵈ where
  inv_inv _ := congrArg toDual (inv_inv _)

@[to_additive]
instance [DivInvMonoid α] : DivInvMonoid αᵒᵈ where
  div_eq_mul_inv _ _ := congrArg toDual (div_eq_mul_inv _ _)

@[to_additive]
instance [DivisionMonoid α] : DivisionMonoid αᵒᵈ where
  mul_inv_rev _ _ := congrArg toDual (mul_inv_rev _ _)
  inv_eq_of_mul _ _ h := congrArg toDual (DivisionMonoid.inv_eq_of_mul _ _ (congrArg ofDual h))

@[to_additive]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ where

@[to_additive]
instance OrderDual.instGroup [Group α] : Group αᵒᵈ where
  inv_mul_cancel _ := congrArg toDual (inv_mul_cancel _)

@[to_additive]
instance [CommGroup α] : CommGroup αᵒᵈ where

@[to_additive (attr := simp)]
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl

@[to_additive (attr := simp)]
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b := rfl

@[to_additive (attr := simp)]
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl

@[to_additive (attr := simp)]
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul]
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul]
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul']
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul']
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl

/-! ### Lexicographical order -/


@[to_additive]
instance [h : One α] : One (Lex α) := h

@[to_additive]
instance [h : Mul α] : Mul (Lex α) := h

@[to_additive]
instance [h : Inv α] : Inv (Lex α) := h

@[to_additive]
instance [h : Div α] : Div (Lex α) := h

@[to_additive (attr := to_additive) (reorder := 1 2) Lex.instSMul]
instance Lex.instPow [h : Pow α β] : Pow (Lex α) β := h

@[to_additive (attr := to_additive) (reorder := 1 2) Lex.instSMul']
instance Lex.instPow' [h : Pow α β] : Pow α (Lex β) := h

@[to_additive]
instance [h : Semigroup α] : Semigroup (Lex α) := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Lex α) := h

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Lex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Lex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup (Lex α) := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass (Lex α) := h

@[to_additive]
instance [h : Monoid α] : Monoid (Lex α) := h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid (Lex α) := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid (Lex α) := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid (Lex α) := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid (Lex α) := h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (Lex α) := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv (Lex α) := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid (Lex α) := h

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid (Lex α) := h

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Lex α) := h

@[to_additive]
instance [h : Group α] : Group (Lex α) := h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Lex α) := h

@[to_additive (attr := simp)]
theorem toLex_one [One α] : toLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl

@[to_additive (attr := simp)]
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl

@[to_additive (attr := simp)]
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl

@[to_additive (attr := simp)]
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl
