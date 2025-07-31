/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Lex
import Mathlib.Data.Prod.Lex

/-!
# Add/Mul equivalence for order type synonyms
-/

variable (α : Type*)

/-- `toLex` as a `MulEquiv`. -/
@[to_additive "`toLex` as a `AddEquiv`."]
def toLexMulEquiv [Mul α] : α ≃* Lex α where
  __ := toLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]
theorem coe_toLexMulEquiv [Mul α] : ⇑(toLexMulEquiv α) = toLex := rfl

@[to_additive (attr := simp)]
theorem coe_symm_toLexMulEquiv [Mul α] : ⇑(toLexMulEquiv α).symm = ofLex := rfl

/-- `ofLex` as a `MulEquiv`. -/
@[to_additive "`ofLex` as a `AddEquiv`."]
def ofLexMulEquiv [Mul α] : Lex α ≃* α where
  __ := ofLex
  map_mul' _ _ := by simp

@[to_additive (attr := simp)]
theorem coe_ofLexMulEquiv [Mul α] : ⇑(ofLexMulEquiv α) = ofLex := rfl

@[to_additive (attr := simp)]
theorem coe_symm_ofLexMulEquiv [Mul α] : ⇑(ofLexMulEquiv α).symm = toLex := rfl

@[simp]
lemma toEquiv_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑(toLexMulEquiv (G × H) : G × H ≃ G ×ₗ H) = toLex :=
  rfl

@[simp]
lemma toEquiv_symm_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑((toLexMulEquiv (G × H)).symm : G ×ₗ H ≃ G × H) = ofLex :=
  rfl
