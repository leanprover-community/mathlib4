/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Characteristic of the order type synonyms

Transfer characteristic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

instance [AddMonoidWithOne R] [CharZero R] : CharZero Rᵒᵈ where
  cast_injective _ _ e := by rw [OrderDual.ext_iff] at e; exact CharZero.cast_injective e

instance {p : ℕ} [AddMonoidWithOne R] [CharP R p] : CharP Rᵒᵈ p where
  cast_eq_zero_iff _ := by rw [OrderDual.ext_iff]; exact CharP.cast_eq_zero_iff ..

instance {p : ℕ} [AddMonoidWithOne R] [h : ExpChar R p] : ExpChar Rᵒᵈ p := by
  rw [expChar_iff]
  cases h with
  | zero => exact .inl ⟨inferInstance, rfl⟩
  | prime pp => exact .inr ⟨pp, inferInstance⟩

@[simp]
theorem ringChar_eq [NonAssocSemiring R] : ringChar Rᵒᵈ = ringChar R :=
  ringChar.eq Rᵒᵈ (ringChar R)

end OrderDual

/-! ### Lexicographical order -/

namespace Lex

instance [AddMonoidWithOne R] [CharZero R] : CharZero (Lex R) := inferInstanceAs <| CharZero R

instance {p : ℕ} [AddMonoidWithOne R] [CharP R p] : CharP (Lex R) p := inferInstanceAs <| CharP R p

instance {p : ℕ} [AddMonoidWithOne R] [ExpChar R p] : ExpChar (Lex R) p :=
  inferInstanceAs <| ExpChar R p

@[simp]
theorem ringChar_eq [NonAssocSemiring R] : ringChar (Lex R) = ringChar R :=
  ringChar.eq (Lex R) (ringChar R)

end Lex
