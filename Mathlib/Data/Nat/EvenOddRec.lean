/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Bitwise

#align_import data.nat.even_odd_rec from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"
/-! # A recursion principle based on even and odd numbers. -/

-- porting note: TODO:
-- Remove dependence on deprecated definitions bit0, bit1.
set_option linter.deprecated false

namespace Nat

/-- Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` for all `n : ℕ`.
This is nothing more than a wrapper around `Nat.binaryRec`, to avoid having to switch to
dealing with `bit0` and `bit1`. -/

@[elab_as_elim]
def evenOddRec {P : ℕ → Sort*} (h0 : P 0) (h_even : ∀ (n) (_ : P n), P (2 * n))
    (h_odd : ∀ (n) (_ : P n), P (2 * n + 1)) (n : ℕ) : P n :=
  binaryRec h0 (fun
    | false, i, hi => (bit0_val i ▸ h_even i hi : P (bit0 i))
    | true, i, hi => (bit1_val i ▸ h_odd i hi : P (bit1 i))) n
#align nat.even_odd_rec Nat.evenOddRec

@[simp]
theorem evenOddRec_zero (P : ℕ → Sort*) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) : @evenOddRec _ h0 h_even h_odd 0 = h0 :=
  binaryRec_zero _ _
#align nat.even_odd_rec_zero Nat.evenOddRec_zero

@[simp]
theorem evenOddRec_even (n : ℕ) (P : ℕ → Sort*) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n) = h_even n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit false n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_even n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binaryRec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit0_val _))
#align nat.even_odd_rec_even Nat.evenOddRec_even

@[simp]
theorem evenOddRec_odd (n : ℕ) (P : ℕ → Sort*) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n + 1) = h_odd n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit true n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_odd n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binaryRec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit1_val _))
#align nat.even_odd_rec_odd Nat.evenOddRec_odd

end Nat
