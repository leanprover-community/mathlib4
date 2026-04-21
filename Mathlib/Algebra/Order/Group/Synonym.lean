/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Lex

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ`, `Lex α`, and `Colex α`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/

namespace OrderDual

@[to_additive]
instance [h : One α] : One αᵒᵈ := h

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ := h

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ := h

@[to_additive]
instance [h : Div α] : Div αᵒᵈ := h

@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul]
instance [h : Pow α β] : Pow αᵒᵈ β := h

@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul']
instance [h : Pow α β] : Pow α βᵒᵈ := h

@[to_additive]
instance [h : Semigroup α] : Semigroup αᵒᵈ where
  mul_assoc := h.mul_assoc

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup αᵒᵈ where
  mul_comm := h.mul_comm

@[to_additive]
instance [Mul α] [h : IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ where
  mul_left_cancel := h.mul_left_cancel

@[to_additive]
instance [Mul α] [h : IsRightCancelMul α] : IsRightCancelMul αᵒᵈ where
  mul_right_cancel := h.mul_right_cancel

@[to_additive]
instance [Mul α] [h : IsCancelMul α] : IsCancelMul αᵒᵈ where

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ where

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ where

@[to_additive]
instance [h : MulOneClass α] : MulOneClass αᵒᵈ where
  one_mul := h.one_mul
  mul_one := h.mul_one

@[to_additive]
instance [h : Monoid α] : Monoid αᵒᵈ where
  npow := h.npow
  npow_succ := h.npow_succ
  npow_zero := h.npow_zero

@[to_additive]
instance [h : CommMonoid α] : CommMonoid αᵒᵈ where

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ where

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid αᵒᵈ where

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid αᵒᵈ where

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ where

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv αᵒᵈ where
  inv_inv := h.inv_inv

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid αᵒᵈ where
  div_eq_mul_inv := h.div_eq_mul_inv
  zpow := h.zpow
  zpow_zero' := h.zpow_zero'
  zpow_succ' := h.zpow_succ'
  zpow_neg' := h.zpow_neg'

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid αᵒᵈ where
  mul_inv_rev := h.mul_inv_rev
  inv_eq_of_mul := h.inv_eq_of_mul

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ where

@[to_additive]
instance [h : Group α] : Group αᵒᵈ where
  inv_mul_cancel := h.inv_mul_cancel

@[to_additive]
instance [h : CommGroup α] : CommGroup αᵒᵈ where

end OrderDual

@[to_additive (attr := simp)]
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl

@[to_additive (attr := simp)] lemma toDual_eq_one [One α] {a : α} : toDual a = 1 ↔ a = 1 := .rfl
@[to_additive (attr := simp)] lemma ofDual_eq_one [One α] {a : αᵒᵈ} : ofDual a = 1 ↔ a = 1 := .rfl

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

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a := .rfl

end Monoid

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

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a := .rfl

end Monoid

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

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a := .rfl

end Monoid
