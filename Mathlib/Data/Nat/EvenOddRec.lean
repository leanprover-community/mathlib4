/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell

! This file was ported from Lean 3 source module data.nat.even_odd_rec
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Bitwise
/-! # A recursion principle based on even and odd numbers. -/

set_option linter.deprecated false
namespace Nat

/-- Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` for all `n : ℕ`.
This is nothing more than a wrapper around `nat.binaryRec`, to avoid having to switch to
dealing with `bit0` and `bit1`. -/

@[elab_as_elim]
def evenOddRec {P : ℕ → Sort _} (h0 : P 0) (h_even : ∀ (n) (_ : P n), P (2 * n))
    (h_odd : ∀ (n) (_ : P n), P (2 * n + 1)) (n : ℕ) : P n :=
  binaryRec h0 (fun
    | false, i, hi => (bit0_val i ▸ h_even i hi : P (bit0 i))
    | true, i, hi => (bit1_val i ▸ h_odd i hi : P (bit1 i))) n
#align nat.even_odd_rec Nat.evenOddRec

@[simp]
theorem even_odd_rec_zero (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) : @evenOddRec _ h0 h_even h_odd 0 = h0 :=
  binary_rec_zero _ _
#align nat.even_odd_rec_zero Nat.even_odd_rec_zero


@[simp]
theorem even_odd_rec_even (n : ℕ) (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n) = h_even n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit false n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_even n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binary_rec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit0_val _))

@[simp]
theorem even_odd_rec_odd (n : ℕ) (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n + 1) = h_odd n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit true n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_odd n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binary_rec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit1_val _))

end Nat
