/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Pairing

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

assert_not_exists Monoid

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

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(Sum.inl x)` to `2 * x` and `(Sum.inr x)` to
`2 * x + 1`.
-/
@[simps! symm_apply]
def natSumNatEquivNat : ℕ ⊕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat

@[simp]
theorem natSumNatEquivNat_apply : ⇑natSumNatEquivNat = Sum.elim (2 * ·) (2 * · + 1) := by
  ext (x | x) <;> rfl

/-- An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat

/-- An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := pairEquiv
    _ ≃ α := e.symm

end Equiv
