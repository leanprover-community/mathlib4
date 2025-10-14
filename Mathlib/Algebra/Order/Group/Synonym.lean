/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Synonym

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ`, `Lex α`, and `Colex α`.
-/


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/


@[to_additive]
instance [h : One α] : One αᵒᵈ := h

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ := h

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ := h

@[to_additive]
instance [h : Div α] : Div αᵒᵈ := h

@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul]
instance OrderDual.instPow [h : Pow α β] : Pow αᵒᵈ β := h

@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul']
instance OrderDual.instPow' [h : Pow α β] : Pow α βᵒᵈ := h

@[to_additive]
instance [h : Semigroup α] : Semigroup αᵒᵈ := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup αᵒᵈ := h

@[to_additive]
instance [Mul α] [h : IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ := h

@[to_additive]
instance [Mul α] [h : IsRightCancelMul α] : IsRightCancelMul αᵒᵈ := h

@[to_additive]
instance [Mul α] [h : IsCancelMul α] : IsCancelMul αᵒᵈ := h

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass αᵒᵈ := h

@[to_additive]
instance [h : Monoid α] : Monoid αᵒᵈ := h

@[to_additive]
instance OrderDual.instCommMonoid [h : CommMonoid α] : CommMonoid αᵒᵈ := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid αᵒᵈ := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid αᵒᵈ := h

@[to_additive]
instance OrderDual.instCancelCommMonoid [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv αᵒᵈ := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid αᵒᵈ := h

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid αᵒᵈ := h

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ := h

@[to_additive]
instance OrderDual.instGroup [h : Group α] : Group αᵒᵈ := h

@[to_additive]
instance [h : CommGroup α] : CommGroup αᵒᵈ := h

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
theorem toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1 := .rfl

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

/-! ### Colexicographical order -/


@[to_additive]
instance [h : One α] : One (Colex α) := h

@[to_additive]
instance [h : Mul α] : Mul (Colex α) := h

@[to_additive]
instance [h : Inv α] : Inv (Colex α) := h

@[to_additive]
instance [h : Div α] : Div (Colex α) := h

@[to_additive (attr := to_additive) (reorder := 1 2) Colex.instSMul]
instance Colex.instPow [h : Pow α β] : Pow (Colex α) β := h

@[to_additive (attr := to_additive) (reorder := 1 2) Colex.instSMul']
instance Colex.instPow' [h : Pow α β] : Pow α (Colex β) := h

@[to_additive]
instance [h : Semigroup α] : Semigroup (Colex α) := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Colex α) := h

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Colex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Colex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup (Colex α) := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup (Colex α) := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass (Colex α) := h

@[to_additive]
instance [h : Monoid α] : Monoid (Colex α) := h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid (Colex α) := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid (Colex α) := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid (Colex α) := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid (Colex α) := h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (Colex α) := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv (Colex α) := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid (Colex α) := h

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid (Colex α) := h

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Colex α) := h

@[to_additive]
instance [h : Group α] : Group (Colex α) := h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Colex α) := h

@[to_additive (attr := simp)]
theorem toColex_one [One α] : toColex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem ofColex_one [One α] : (ofColex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b := rfl

@[to_additive (attr := simp)]
theorem ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofColex b := rfl

@[to_additive (attr := simp)]
theorem toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toColex_div [Div α] (a b : α) : toColex (a / b) = toColex a / toColex b := rfl

@[to_additive (attr := simp)]
theorem ofColex_div [Div α] (a b : Colex α) : ofColex (a / b) = ofColex a / ofColex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]
theorem toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]
theorem ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']
theorem pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']
theorem pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b := rfl
