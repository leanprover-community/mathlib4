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

public section


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/

namespace OrderDual

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [One α] : One αᵒᵈ := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Mul α] : Mul αᵒᵈ := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Inv α] : Inv αᵒᵈ := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Div α] : Div αᵒᵈ := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul]
instance [Pow α β] : Pow αᵒᵈ β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul']
instance [Pow α β] : Pow α βᵒᵈ := inferInstanceAs <| Pow α β

@[to_additive] instance [Semigroup α] : Semigroup αᵒᵈ := inferInstanceAs <| Semigroup α

@[to_additive] instance [CommSemigroup α] : CommSemigroup αᵒᵈ := inferInstanceAs <| CommSemigroup α

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul αᵒᵈ where

@[to_additive]
instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ where

@[to_additive]
instance [RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ where

@[to_additive]
instance [MulOneClass α] : MulOneClass αᵒᵈ := inferInstanceAs <| MulOneClass α

@[to_additive]
instance [Monoid α] : Monoid αᵒᵈ := inferInstanceAs <| Monoid α

@[to_additive]
instance [CommMonoid α] : CommMonoid αᵒᵈ := inferInstanceAs <| CommMonoid α

@[to_additive]
instance [LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
instance [RightCancelMonoid α] : RightCancelMonoid αᵒᵈ := inferInstanceAs <| RightCancelMonoid α

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵒᵈ := inferInstanceAs <| CancelMonoid α

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid αᵒᵈ := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv αᵒᵈ := inferInstanceAs <| InvolutiveInv α

@[to_additive]
instance [DivInvMonoid α] : DivInvMonoid αᵒᵈ := inferInstanceAs <| DivInvMonoid α

@[to_additive]
instance [DivisionMonoid α] : DivisionMonoid αᵒᵈ := inferInstanceAs <| DivisionMonoid α

@[to_additive]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
instance [Group α] : Group αᵒᵈ := inferInstanceAs <| Group α

@[to_additive]
instance [CommGroup α] : CommGroup αᵒᵈ := inferInstanceAs <| CommGroup α

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


namespace Lex

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [One α] : One (Lex α) := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Mul α] : Mul (Lex α) := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Inv α] : Inv (Lex α) := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Div α] : Div (Lex α) := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
instance [Pow α β] : Pow (Lex α) β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
instance [Pow α β] : Pow α (Lex β) := inferInstanceAs <| Pow α β

@[to_additive]
instance [Semigroup α] : Semigroup (Lex α) := inferInstanceAs <| Semigroup α

@[to_additive]
instance [CommSemigroup α] : CommSemigroup (Lex α) := inferInstanceAs <| CommSemigroup α

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
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) :=
  inferInstanceAs <| LeftCancelSemigroup α

@[to_additive]
instance [RightCancelSemigroup α] : RightCancelSemigroup (Lex α) :=
  inferInstanceAs <| RightCancelSemigroup α

@[to_additive]
instance [MulOneClass α] : MulOneClass (Lex α) := inferInstanceAs <| MulOneClass α

@[to_additive]
instance [Monoid α] : Monoid (Lex α) := inferInstanceAs <| Monoid α

@[to_additive]
instance [CommMonoid α] : CommMonoid (Lex α) := inferInstanceAs <| CommMonoid α

@[to_additive]
instance [LeftCancelMonoid α] : LeftCancelMonoid (Lex α) := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
instance [RightCancelMonoid α] : RightCancelMonoid (Lex α) := inferInstanceAs <| RightCancelMonoid α

@[to_additive]
instance [CancelMonoid α] : CancelMonoid (Lex α) := inferInstanceAs <| CancelMonoid α

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid (Lex α) := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv (Lex α) := inferInstanceAs <| InvolutiveInv α

@[to_additive]
instance [DivInvMonoid α] : DivInvMonoid (Lex α) := inferInstanceAs <| DivInvMonoid α

@[to_additive]
instance [DivisionMonoid α] : DivisionMonoid (Lex α) := inferInstanceAs <| DivisionMonoid α

@[to_additive]
instance [DivisionCommMonoid α] : DivisionCommMonoid (Lex α) :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
instance [Group α] : Group (Lex α) := inferInstanceAs <| Group α

@[to_additive]
instance [CommGroup α] : CommGroup (Lex α) := inferInstanceAs <| CommGroup α

end Lex

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


namespace Colex

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [One α] : One (Colex α) := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Mul α] : Mul (Colex α) := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Inv α] : Inv (Colex α) := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive] instance [Div α] : Div (Colex α) := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
instance [Pow α β] : Pow (Colex α) β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
instance [Pow α β] : Pow α (Colex β) := inferInstanceAs <| Pow α β

@[to_additive]
instance [Semigroup α] : Semigroup (Colex α) := inferInstanceAs <| Semigroup α

@[to_additive]
instance [CommSemigroup α] : CommSemigroup (Colex α) := inferInstanceAs <| CommSemigroup α

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
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Colex α) :=
  inferInstanceAs <| LeftCancelSemigroup α

@[to_additive]
instance [RightCancelSemigroup α] : RightCancelSemigroup (Colex α) :=
  inferInstanceAs <| RightCancelSemigroup α

@[to_additive]
instance [MulOneClass α] : MulOneClass (Colex α) := inferInstanceAs <| MulOneClass α

@[to_additive]
instance [Monoid α] : Monoid (Colex α) := inferInstanceAs <| Monoid α

@[to_additive]
instance [CommMonoid α] : CommMonoid (Colex α) := inferInstanceAs <| CommMonoid α

@[to_additive]
instance [LeftCancelMonoid α] : LeftCancelMonoid (Colex α) := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
instance [RightCancelMonoid α] : RightCancelMonoid (Colex α) :=
  inferInstanceAs <| RightCancelMonoid α

@[to_additive]
instance [CancelMonoid α] : CancelMonoid (Colex α) := inferInstanceAs <| CancelMonoid α

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid (Colex α) := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv (Colex α) := inferInstanceAs <| InvolutiveInv α

@[to_additive]
instance [DivInvMonoid α] : DivInvMonoid (Colex α) := inferInstanceAs <| DivInvMonoid α

@[to_additive]
instance [DivisionMonoid α] : DivisionMonoid (Colex α) := inferInstanceAs <| DivisionMonoid α

@[to_additive]
instance [DivisionCommMonoid α] : DivisionCommMonoid (Colex α) :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
instance [Group α] : Group (Colex α) := inferInstanceAs <| Group α

@[to_additive]
instance [CommGroup α] : CommGroup (Colex α) := inferInstanceAs <| CommGroup α

end Colex

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
