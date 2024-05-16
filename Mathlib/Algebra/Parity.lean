/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Set.Defs

#align_import algebra.parity from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!  # Squares, even and odd elements

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `IsSquare` and we let `Even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
IsSquare a ↔ ∃ r, a = r * r
Even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `IsSquare/Even`.
  For instance, in some cases, there are `Semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `Odd` to a separate file.
* TODO: The "old" definition of `Even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/


open MulOpposite

variable {F α β R : Type*}

set_option linter.deprecated false in
theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl
#align even_iff_exists_bit0 even_iff_exists_bit0

alias ⟨Even.exists_bit0, _⟩ := even_iff_exists_bit0
#align even.exists_bit0 Even.exists_bit0

section Semiring

variable [Semiring α] [Semiring β] {a b : α} {n : ℕ}

section WithOdd

@[simp] lemma one_add_self_self : Odd (1 + a + a) := by simp [add_comm 1 a]

end WithOdd

end Semiring

section Ring

variable [Ring α] {a b : α} {n : ℕ}

theorem odd_abs [LinearOrder α] : Odd (abs a) ↔ Odd a := by
  cases' abs_choice a with h h <;> simp only [h, odd_neg]
#align odd_abs odd_abs

end Ring
