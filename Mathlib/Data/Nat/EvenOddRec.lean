/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell

! This file was ported from Lean 3 source module data.nat.even_odd_rec
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Init.Data.Nat.Bitwise
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
def evenOddRec {P : ℕ → Sort _} (h0 : P 0) (h_even : ∀ (n) (_ : P n), P (2 * n))
    (h_odd : ∀ (n) (_ : P n), P (2 * n + 1)) (n : ℕ) : P n :=
  binaryRec h0 (fun
    | false, i, hi => (bit0_val i ▸ h_even i hi : P (bit0 i))
    | true, i, hi => (bit1_val i ▸ h_odd i hi : P (bit1 i))) n
#align nat.even_odd_rec Nat.evenOddRec

@[simp]
theorem evenOddRec_zero (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) : @evenOddRec _ h0 h_even h_odd 0 = h0 :=
  binaryRec_zero _ _
#align nat.even_odd_rec_zero Nat.evenOddRec_zero

@[simp]
theorem evenOddRec_even (n : ℕ) (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n) = h_even n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit false n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_even n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binaryRec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit0_val _))
#align nat.even_odd_rec_even Nat.evenOddRec_even

@[simp]
theorem evenOddRec_odd (n : ℕ) (P : ℕ → Sort _) (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) :
    @evenOddRec _ h0 h_even h_odd (2 * n + 1) = h_odd n (evenOddRec h0 h_even h_odd n) :=
  have : ∀ a, bit true n = a →
      HEq (@evenOddRec _ h0 h_even h_odd a) (h_odd n (evenOddRec h0 h_even h_odd n))
    | _, rfl => by rw [evenOddRec, binaryRec_eq]; apply eq_rec_heq; exact H
  eq_of_heq (this _ (bit1_val _))
#align nat.even_odd_rec_odd Nat.evenOddRec_odd

/-- Strong recursion principle on even and odd numbers: if for all `i : ℕ` we can prove `P (2 * i)`
from `P j` for all `j < 2 * i` and we can prove `P (2 * i + 1)` from `P j` for all `j < 2 * i + 1`,
then we have `P n` for all `n : ℕ`. -/
noncomputable
def evenOddStrongRec {p : Sort _} (n : ℕ)
    (peven : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m → p) → p)
    (podd : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m + 1 → p) → p) : p :=
n.strongRecOn' <| fun m ih => m.even_or_odd'.choose_spec.by_cases
  (fun hm => peven m.even_or_odd'.choose <| fun k hk => ih k <| hm.symm ▸ hk)
  (fun hm => podd m.even_or_odd'.choose <| fun k hk => ih k <| hm.symm ▸ hk)

@[simp]
lemma evenOddStrongRec_even {p : Sort _} (m : ℕ)
    (peven : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m → p) → p)
    (podd : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m + 1 → p) → p) :
    (2 * m).evenOddStrongRec peven podd =
      peven m (fun k _ => k.evenOddStrongRec peven podd) := by
  rcases (2 * m).even_or_odd'.choose_spec with h | h
  · rw [evenOddStrongRec, strongRecOn'_beta, Or.by_cases, dif_pos h]
    conv_rhs => rw [mul_left_cancel₀ two_ne_zero h]
  · exact (two_mul_ne_two_mul_add_one h).elim

@[simp]
lemma evenOddStrongRec_odd {p : Sort _} (m : ℕ)
    (peven : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m → p) → p)
    (podd : ∀ m : ℕ, (∀ k : ℕ, k < 2 * m + 1 → p) → p) :
    (2 * m + 1).evenOddStrongRec peven podd =
      podd m (fun k _ => k.evenOddStrongRec peven podd) := by
  rcases (2 * m + 1).even_or_odd'.choose_spec with h | h
  · exact (two_mul_ne_two_mul_add_one h.symm).elim
  · rw [evenOddStrongRec, strongRecOn'_beta, Or.by_cases, dif_neg two_mul_ne_two_mul_add_one.symm]
    conv_rhs => rw [mul_left_cancel₀ two_ne_zero <| succ_injective h]

end Nat
