/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.CharP.Defs

/-!
# Characteristic of the order type synonyms

Transfer characteristic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

instance [AddMonoidWithOne R] [CharZero R] : CharZero Rᵒᵈ := inferInstanceAs <| CharZero R

instance {p : ℕ} [AddMonoidWithOne R] [CharP R p] : CharP Rᵒᵈ p := inferInstanceAs <| CharP R p

instance {p : ℕ} [AddMonoidWithOne R] [ExpChar R p] : ExpChar Rᵒᵈ p :=
  inferInstanceAs <| ExpChar R p

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
