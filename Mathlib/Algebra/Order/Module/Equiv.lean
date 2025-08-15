/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Order.Group.Equiv
import Mathlib.Algebra.Order.Module.Synonym

/-!
# Linear equivalence for order type synonyms
-/

variable (α β : Type*)
variable [Semiring α] [AddCommMonoid β] [Module α β]

/-- `toLex` as a linear equivalence -/
def toLexLinearEquiv : β ≃ₗ[α] Lex β := (toLexAddEquiv β).toLinearEquiv toLex_smul

/-- `ofLex` as a linear equivalence -/
def ofLexLinearEquiv : Lex β ≃ₗ[α] β := (ofLexAddEquiv β).toLinearEquiv ofLex_smul

@[simp] lemma coe_toLexLinearEquiv : ⇑(toLexLinearEquiv α β) = toLex := rfl
@[simp] lemma coe_ofLexLinearEquiv : ⇑(ofLexLinearEquiv α β) = ofLex := rfl

@[simp] lemma symm_toLexLinearEquiv : (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β := rfl
@[simp] lemma symm_ofLexLinearEquiv : (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β := rfl
