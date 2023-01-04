/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies

! This file was ported from Lean 3 source module algebra.group.order_synonym
! leanprover-community/mathlib commit d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Synonym

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `lex α`.
-/


open OrderDual

variable {α β : Type _}

/-! ### `OrderDual` -/


@[to_additive]
instance [h : One α] : One αᵒᵈ := h

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ := h

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ := h

@[to_additive]
instance [h : Div α] : Div αᵒᵈ := h

@[to_additive (reorder := 1)]
instance [h : Pow α β] : Pow αᵒᵈ β := h
#align order_dual.has_pow instPowOrderDual
#align order_dual.has_smul instSMulOrderDual

@[to_additive (reorder := 1)]
instance instPowOrderDual' [h : Pow α β] : Pow α βᵒᵈ := h
#align order_dual.has_pow' instPowOrderDual'
#align order_dual.has_smul' instSMulOrderDual'

@[to_additive]
instance [h : Semigroup α] : Semigroup αᵒᵈ := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup αᵒᵈ := h

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass αᵒᵈ := h

@[to_additive]
instance [h : Monoid α] : Monoid αᵒᵈ := h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid αᵒᵈ := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid αᵒᵈ := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid αᵒᵈ := h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv αᵒᵈ := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid αᵒᵈ := h

@[to_additive OrderDual.subtractionMonoid]
instance [h : DivisionMonoid α] : DivisionMonoid αᵒᵈ := h

@[to_additive OrderDual.subtractionCommMonoid]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ := h

@[to_additive]
instance [h : Group α] : Group αᵒᵈ := h
#align order_dual.group instGroupOrderDual
#align order_dual.add_group instAddGroupOrderDual

@[to_additive]
instance [h : CommGroup α] : CommGroup αᵒᵈ := h

@[simp, to_additive]
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl
#align to_dual_one toDual_one

@[simp, to_additive]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl
#align of_dual_one ofDual_one

@[simp, to_additive]
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl
#align to_dual_mul toDual_mul

@[simp, to_additive]
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b := rfl
#align of_dual_mul ofDual_mul

@[simp, to_additive]
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl
#align to_dual_inv toDual_inv

@[simp, to_additive]
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl
#align of_dual_inv ofDual_inv

@[simp, to_additive]
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl
#align to_dual_div toDual_div

@[simp, to_additive]
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl
#align of_dual_div ofDual_div

@[simp, to_additive (reorder := 1 4)]
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl
#align to_dual_pow toDual_pow

@[simp, to_additive (reorder := 1 4)]
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b := rfl
#align of_dual_pow ofDual_pow

@[simp, to_additive (reorder := 1 4) toDual_smul']
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl
#align pow_to_dual pow_toDual

@[simp, to_additive (reorder := 1 4) ofDual_smul']
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl
#align pow_of_dual pow_ofDual

/-! ### Lexicographical order -/


@[to_additive]
instance [h : One α] : One (Lex α) := h

@[to_additive]
instance [h : Mul α] : Mul (Lex α) := h

@[to_additive]
instance [h : Inv α] : Inv (Lex α) := h

@[to_additive]
instance [h : Div α] : Div (Lex α) := h

@[to_additive (reorder := 1)]
instance [h : Pow α β] : Pow (Lex α) β := h
#align lex.has_pow instPowLex
#align lex.has_smul instSMulLex

@[to_additive (reorder := 1)]
instance instPowLex' [h : Pow α β] : Pow α (Lex β) := h
#align lex.has_pow' instPowLex'
#align lex.has_smul' instSMulLex'

@[to_additive]
instance [h : Semigroup α] : Semigroup (Lex α) := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Lex α) := h

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

@[to_additive OrderDual.subtractionMonoid]
instance [h : DivisionMonoid α] : DivisionMonoid (Lex α) := h

@[to_additive OrderDual.subtractionCommMonoid]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Lex α) := h

@[to_additive]
instance [h : Group α] : Group (Lex α) := h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Lex α) := h

@[simp, to_additive]
theorem toLex_one [One α] : toLex (1 : α) = 1 := rfl
#align to_lex_one toLex_one

@[simp, to_additive]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl
#align of_lex_one ofLex_one

@[simp, to_additive]
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl
#align to_lex_mul toLex_mul

@[simp, to_additive]
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl
#align of_lex_mul ofLex_mul

@[simp, to_additive]
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl
#align to_lex_inv toLex_inv

@[simp, to_additive]
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl
#align of_lex_inv ofLex_inv

@[simp, to_additive]
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl
#align to_lex_div toLex_div

@[simp, to_additive]
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl
#align of_lex_div ofLex_div

@[simp, to_additive (reorder := 1 4)]
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl
#align to_lex_pow toLex_pow

@[simp, to_additive (reorder := 1 4)]
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl
#align of_lex_pow ofLex_pow

@[simp, to_additive (reorder := 1 4) toLex_smul']
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl
#align pow_to_lex pow_toLex

@[simp, to_additive (reorder := 1 4) ofLex_smul']
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl
#align pow_of_lex pow_ofLex

attribute [to_additive] instSMulOrderDual instSMulOrderDual'
  toDual_smul ofDual_smul toDual_smul' ofDual_smul'
  instSMulLex instSMulLex'
  toLex_smul ofLex_smul toLex_smul' ofLex_smul'
