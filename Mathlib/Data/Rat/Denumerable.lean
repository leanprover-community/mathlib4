/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.SetTheory.Cardinal.Basic

#align_import data.rat.denumerable from "leanprover-community/mathlib"@"dde670c9a3f503647fd5bfdf1037bad526d3397a"

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/

assert_not_exists Module
assert_not_exists Field

namespace Rat

open Denumerable

instance : Infinite ℚ :=
  Infinite.of_injective ((↑) : ℕ → ℚ) Nat.cast_injective

private def denumerable_aux : ℚ ≃ { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 } where
  toFun x := ⟨⟨x.1, x.2⟩, Nat.pos_of_ne_zero x.3, x.4⟩
  invFun x := ⟨x.1.1, x.1.2, ne_zero_of_lt x.2.1, x.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ := by
  let T := { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 }
  letI : Infinite T := Infinite.of_injective _ denumerable_aux.injective
  letI : Encodable T := Subtype.encodable
  letI : Denumerable T := ofEncodableOfInfinite T
  exact Denumerable.ofEquiv T denumerable_aux

end Rat

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := by simp only [mk_eq_aleph0]
#align cardinal.mk_rat Cardinal.mkRat
