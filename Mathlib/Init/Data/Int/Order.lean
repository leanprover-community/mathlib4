/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Order.Defs

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# The order relation on the integers
-/

open Nat

namespace Int

export private decNonneg from Init.Data.Int.Basic

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

instance instLinearOrder : LinearOrder ℤ where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidableEq := by infer_instance
  decidableLE := by infer_instance
  decidableLT := by infer_instance

@[deprecated (since := "2024-07-27")] alias mul_neg_eq_neg_mul_symm := Int.mul_neg
@[deprecated (since := "2024-07-27")] alias neg_mul_eq_neg_mul_symm := Int.neg_mul

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  Int.mul_eq_zero.mp h

end Int
