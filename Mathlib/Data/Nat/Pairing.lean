/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Notation.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Set.Lattice.Image

/-!
# Naturals pairing function

This file defines a pairing function for the naturals as follows:
```text
 0  1  4  9 16
 2  3  5 10 17
 6  7  8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/

assert_not_exists Monoid

open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot]
def pair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot]
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
theorem pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s ≤ s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
    simp [s, pair, hl.not_gt, Nat.add_assoc, Nat.add_sub_cancel' (le_of_not_gt h), sm]

theorem pair_eq_of_unpair_eq {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n

@[deprecated (since := "2025-05-24")]
alias pair_unpair' := pair_eq_of_unpair_eq

@[simp]
theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact Nat.add_le_add_left (le_of_not_gt h) _
    simp [unpair, ae, Nat.add_assoc, Nat.add_sub_cancel_left]

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps -fullyApplied]
def pairEquiv : ℕ × ℕ ≃ ℕ :=
  ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩

theorem surjective_unpair : Surjective unpair :=
  pairEquiv.symm.surjective

@[simp]
theorem pair_eq_pair {a b c d : ℕ} : pair a b = pair c d ↔ a = c ∧ b = d :=
  pairEquiv.injective.eq_iff.trans (@Prod.ext_iff ℕ ℕ (a, b) (c, d))

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n := by
  let s := sqrt n
  simp only [unpair]
  by_cases h : n - s * s < s <;> simp [s, h, ↓reduceIte]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp only [not_lt] at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (Nat.sub_lt n1 (Nat.mul_pos s0 s0))

@[simp]
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  simp

theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
  | 0 => by simp
  | _ + 1 => le_of_lt (unpair_lt (Nat.succ_pos _))

theorem left_le_pair (a b : ℕ) : a ≤ pair a b := by simpa using unpair_left_le (pair a b)

theorem right_le_pair (a b : ℕ) : b ≤ pair a b := by
  by_cases h : a < b
  · simpa [pair, h] using le_trans (le_mul_self _) (Nat.le_add_right _ _)
  · simp [pair, h]

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n := by
  simpa using right_le_pair n.unpair.1 n.unpair.2

theorem pair_lt_pair_left {a₁ a₂} (b) (h : a₁ < a₂) : pair a₁ b < pair a₂ b := by
  by_cases h₁ : a₁ < b <;> simp [pair, h₁, Nat.add_assoc]
  · by_cases h₂ : a₂ < b <;> simp [h₂, h]
    simp? at h₂ says simp only [not_lt] at h₂
    apply Nat.add_lt_add_of_le_of_lt
    · exact Nat.mul_self_le_mul_self h₂
    · exact Nat.lt_add_right _ h
  · simp at h₁
    simp only [not_lt_of_gt (lt_of_le_of_lt h₁ h), ite_false]
    apply add_lt_add
    · exact Nat.mul_self_lt_mul_self h
    · apply Nat.add_lt_add_right; assumption

theorem pair_lt_pair_right (a) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂ := by
  by_cases h₁ : a < b₁
  · simpa [pair, h₁, Nat.add_assoc, lt_trans h₁ h, h] using mul_self_lt_mul_self h
  · simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
    by_cases h₂ : a < b₂ <;> simp [h₂, h]
    simp? at h₁ says simp only [not_lt] at h₁
    rw [Nat.add_comm, Nat.add_comm _ a, Nat.add_assoc, Nat.add_lt_add_iff_left]
    rwa [Nat.add_comm, ← sqrt_lt, sqrt_add_eq]
    exact le_trans h₁ (Nat.le_add_left _ _)

theorem pair_lt_max_add_one_sq (m n : ℕ) : pair m n < (max m n + 1) ^ 2 := by
  simp only [pair, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
  split_ifs <;> simp [Nat.le_of_lt, not_lt.1, *] <;> omega

theorem max_sq_add_min_le_pair (m n : ℕ) : max m n ^ 2 + min m n ≤ pair m n := by
  rw [pair]
  rcases lt_or_ge m n with h | h
  · rw [if_pos h, max_eq_right h.le, min_eq_left h.le, Nat.pow_two]
  rw [if_neg h.not_gt, max_eq_left h, min_eq_right h, Nat.pow_two, Nat.add_assoc,
    Nat.add_le_add_iff_left]
  exact Nat.le_add_left _ _

theorem add_le_pair (m n : ℕ) : m + n ≤ pair m n := by
  simp only [pair, Nat.add_assoc]
  split_ifs
  · have := le_mul_self n
    omega
  · exact Nat.le_add_left _ _

theorem unpair_add_le (n : ℕ) : (unpair n).1 + (unpair n).2 ≤ n :=
  (add_le_pair _ _).trans_eq (pair_unpair _)

end Nat

open Nat

section CompleteLattice

theorem iSup_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    ⨆ n : ℕ, f n.unpair.1 n.unpair.2 = ⨆ (i : ℕ) (j : ℕ), f i j := by
  rw [← (iSup_prod : ⨆ i : ℕ × ℕ, f i.1 i.2 = _), ← Nat.surjective_unpair.iSup_comp]

theorem iInf_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    ⨅ n : ℕ, f n.unpair.1 n.unpair.2 = ⨅ (i : ℕ) (j : ℕ), f i j :=
  iSup_unpair (show ℕ → ℕ → αᵒᵈ from f)

end CompleteLattice

namespace Set

theorem iUnion_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
    ⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Set.iUnion_prod]
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)

theorem iUnion_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋃ n : ℕ, f n.unpair.1 n.unpair.2 = ⋃ (i : ℕ) (j : ℕ), f i j :=
  iSup_unpair f

theorem iInter_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋂ n : ℕ, f n.unpair.1 n.unpair.2 = ⋂ (i : ℕ) (j : ℕ), f i j :=
  iInf_unpair f

end Set
