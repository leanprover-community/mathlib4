/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Eric Wieser

! This file was ported from Lean 3 source module char_p_zero_ne_char_zero
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.CharP.Basic

/-! # `CharP R 0` and `CharZero R` need not coincide for semirings

For rings, the two notions coincide.

In fact, `CharP.ofCharZero` shows that `CharZero R` implies `CharP R 0` for any `CharZero`
`AddMonoid R` with `1`.
The reverse implication holds for any `AddLeftCancelMonoid R` with `1`, by `charP_to_charZero`.

This file shows that there are semirings `R` for which `CharP R 0` holds and `CharZero R` does not.

The example is `{0, 1}` with saturating addition.
-/


namespace Counterexample

@[simp]
theorem add_one_eq_one (x : WithZero Unit) : x + 1 = 1 :=
  WithZero.cases_on x (by rfl) fun h => by rfl
#align counterexample.add_one_eq_one Counterexample.add_one_eq_one

theorem withZero_unit_charP_zero : CharP (WithZero Unit) 0 :=
  ⟨fun x => by cases x <;> simp⟩
#align counterexample.with_zero_unit_char_p_zero Counterexample.withZero_unit_charP_zero

theorem withZero_unit_not_charZero : ¬CharZero (WithZero Unit) := fun ⟨h⟩ =>
  h.ne (by simp : 1 + 1 ≠ 0 + 1) (by simp)
#align counterexample.with_zero_unit_not_char_zero Counterexample.withZero_unit_not_charZero

end Counterexample
