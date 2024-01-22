/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Pairing

#align_import logic.equiv.nat from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/


open Nat Function

namespace Equiv

variable {α : Type*}

/-- An equivalence between `Bool × ℕ` and `ℕ`, by mapping `(true, x)` to `2 * x + 1` and
`(false, x)` to `2 * x`. -/
@[simps]
def boolProdNatEquivNat : Bool × ℕ ≃ ℕ where
  toFun := uncurry bit
  invFun := boddDiv2
  left_inv := fun ⟨b, n⟩ => by simp only [bodd_bit, div2_bit, uncurry_apply_pair, boddDiv2_eq]
  right_inv n := by simp only [bit_decomp, boddDiv2_eq, uncurry_apply_pair]
#align equiv.bool_prod_nat_equiv_nat Equiv.boolProdNatEquivNat
#align equiv.bool_prod_nat_equiv_nat_symm_apply Equiv.boolProdNatEquivNat_symm_apply
#align equiv.bool_prod_nat_equiv_nat_apply Equiv.boolProdNatEquivNat_apply

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(Sum.inl x)` to `2 * x` and `(Sum.inr x)` to
`2 * x + 1`.
-/
@[simps! symm_apply]
def natSumNatEquivNat : ℕ ⊕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat
#align equiv.nat_sum_nat_equiv_nat Equiv.natSumNatEquivNat
#align equiv.nat_sum_nat_equiv_nat_symm_apply Equiv.natSumNatEquivNat_symm_apply

set_option linter.deprecated false in
@[simp]
theorem natSumNatEquivNat_apply : ⇑natSumNatEquivNat = Sum.elim bit0 bit1 := by
  ext (x | x) <;> rfl
#align equiv.nat_sum_nat_equiv_nat_apply Equiv.natSumNatEquivNat_apply

/-- An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat
#align equiv.int_equiv_nat Equiv.intEquivNat

/-- An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := pairEquiv
    _ ≃ α := e.symm
#align equiv.prod_equiv_of_equiv_nat Equiv.prodEquivOfEquivNat

end Equiv
