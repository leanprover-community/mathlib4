/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.MinMax

#align_import data.nat.pairing from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
#  Naturals pairing function

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


open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
-- porting notes: no pp_nodot
--@[pp_nodot]
def pair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b
#align nat.mkpair Nat.pair

/-- Unpairing function for the natural numbers. -/
-- porting notes: no pp_nodot
--@[pp_nodot]
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)
#align nat.unpair Nat.unpair

@[simp]
theorem pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  -- ⊢ pair (if n - sqrt n * sqrt n < sqrt n then (n - sqrt n * sqrt n, sqrt n) els …
                       -- ⊢ pair (if n - sqrt n * sqrt n < sqrt n then (n - sqrt n * sqrt n, sqrt n) els …
  have sm : s * s + (n - s * s) = n := add_tsub_cancel_of_le (sqrt_le _)
  -- ⊢ pair (if n - sqrt n * sqrt n < sqrt n then (n - sqrt n * sqrt n, sqrt n) els …
  split_ifs with h
  -- ⊢ pair (n - sqrt n * sqrt n, sqrt n).fst (n - sqrt n * sqrt n, sqrt n).snd = n
  · simp [pair, h, sm]
    -- 🎉 no goals
  · have hl : n - s * s - s ≤ s :=
      tsub_le_iff_left.mpr (tsub_le_iff_left.mpr <| by rw [← add_assoc]; apply sqrt_le_add)
    simp [pair, hl.not_lt, add_assoc, add_tsub_cancel_of_le (le_of_not_gt h), sm]
    -- 🎉 no goals
#align nat.mkpair_unpair Nat.pair_unpair

theorem pair_unpair' {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n
  -- 🎉 no goals
#align nat.mkpair_unpair' Nat.pair_unpair'

@[simp]
theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split_ifs with h
  -- ⊢ unpair (if a < b then b * b + a else a * a + a + b) = (a, b)
                     -- ⊢ unpair (b * b + a) = (a, b)
  · show unpair (b * b + a) = (a, b)
    -- ⊢ unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    -- ⊢ unpair (b * b + a) = (a, b)
    simp [unpair, be, add_tsub_cancel_right, h]
    -- 🎉 no goals
  · show unpair (a * a + a + b) = (a, b)
    -- ⊢ unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact add_le_add_left (le_of_not_gt h) _
    simp [unpair, ae, Nat.not_lt_zero, add_assoc]
    -- 🎉 no goals
#align nat.unpair_mkpair Nat.unpair_pair

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps (config := { fullyApplied := false })]
def pairEquiv : ℕ × ℕ ≃ ℕ :=
  ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩
#align nat.mkpair_equiv Nat.pairEquiv
#align nat.mkpair_equiv_apply Nat.pairEquiv_apply
#align nat.mkpair_equiv_symm_apply Nat.pairEquiv_symm_apply

theorem surjective_unpair : Surjective unpair :=
  pairEquiv.symm.surjective
#align nat.surjective_unpair Nat.surjective_unpair

@[simp]
theorem pair_eq_pair {a b c d : ℕ} : pair a b = pair c d ↔ a = c ∧ b = d :=
  pairEquiv.injective.eq_iff.trans (@Prod.ext_iff ℕ ℕ (a, b) (c, d))
#align nat.mkpair_eq_mkpair Nat.pair_eq_pair

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n := by
  let s := sqrt n
  -- ⊢ (unpair n).fst < n
  simp [unpair]
  -- ⊢ (if n - sqrt n * sqrt n < sqrt n then (n - sqrt n * sqrt n, sqrt n) else (sq …
  by_cases h : n - s * s < s <;> simp [h]
  -- ⊢ (if n - sqrt n * sqrt n < sqrt n then (n - sqrt n * sqrt n, sqrt n) else (sq …
                                 -- ⊢ n - sqrt n * sqrt n < n
                                 -- ⊢ sqrt n < n
  · exact lt_of_lt_of_le h (sqrt_le_self _)
    -- 🎉 no goals
  · simp at h
    -- ⊢ sqrt n < n
    have s0 : 0 < s := sqrt_pos.2 n1
    -- ⊢ sqrt n < n
    exact lt_of_le_of_lt h (tsub_lt_self n1 (mul_pos s0 s0))
    -- 🎉 no goals
#align nat.unpair_lt Nat.unpair_lt

@[simp]
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  -- ⊢ (let s := sqrt 0;
  simp
  -- 🎉 no goals
#align nat.unpair_zero Nat.unpair_zero

theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 => le_of_lt (unpair_lt (Nat.succ_pos _))
#align nat.unpair_left_le Nat.unpair_left_le

theorem left_le_pair (a b : ℕ) : a ≤ pair a b := by simpa using unpair_left_le (pair a b)
                                                    -- 🎉 no goals
#align nat.left_le_mkpair Nat.left_le_pair

theorem right_le_pair (a b : ℕ) : b ≤ pair a b := by
  by_cases h : a < b <;> simp [pair, h]
  -- ⊢ b ≤ pair a b
                         -- ⊢ b ≤ b * b + a
                         -- 🎉 no goals
  exact le_trans (le_mul_self _) (Nat.le_add_right _ _)
  -- 🎉 no goals
#align nat.right_le_mkpair Nat.right_le_pair

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n := by
  simpa using right_le_pair n.unpair.1 n.unpair.2
  -- 🎉 no goals
#align nat.unpair_right_le Nat.unpair_right_le

theorem pair_lt_pair_left {a₁ a₂} (b) (h : a₁ < a₂) : pair a₁ b < pair a₂ b := by
  by_cases h₁ : a₁ < b <;> simp [pair, h₁, add_assoc]
  -- ⊢ pair a₁ b < pair a₂ b
                           -- ⊢ b * b + a₁ < if a₂ < b then b * b + a₂ else a₂ * a₂ + (a₂ + b)
                           -- ⊢ a₁ * a₁ + (a₁ + b) < if a₂ < b then b * b + a₂ else a₂ * a₂ + (a₂ + b)
  · by_cases h₂ : a₂ < b <;> simp [pair, h₂, h]
    -- ⊢ b * b + a₁ < if a₂ < b then b * b + a₂ else a₂ * a₂ + (a₂ + b)
                             -- 🎉 no goals
                             -- ⊢ b * b + a₁ < a₂ * a₂ + (a₂ + b)
    simp at h₂
    -- ⊢ b * b + a₁ < a₂ * a₂ + (a₂ + b)
    apply add_lt_add_of_le_of_lt
    -- ⊢ b * b ≤ a₂ * a₂
    exact mul_self_le_mul_self h₂
    -- ⊢ a₁ < a₂ + b
    exact Nat.lt_add_right _ _ _ h
    -- 🎉 no goals
  · simp at h₁
    -- ⊢ a₁ * a₁ + (a₁ + b) < if a₂ < b then b * b + a₂ else a₂ * a₂ + (a₂ + b)
    simp [not_lt_of_gt (lt_of_le_of_lt h₁ h)]
    -- ⊢ a₁ * a₁ + (a₁ + b) < a₂ * a₂ + (a₂ + b)
    apply add_lt_add
    -- ⊢ a₁ * a₁ < a₂ * a₂
    exact mul_self_lt_mul_self h
    -- ⊢ a₁ + b < a₂ + b
    apply add_lt_add_right; assumption
    -- ⊢ a₁ < a₂
                            -- 🎉 no goals
#align nat.mkpair_lt_mkpair_left Nat.pair_lt_pair_left

theorem pair_lt_pair_right (a) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂ := by
  by_cases h₁ : a < b₁ <;> simp [pair, h₁, add_assoc]
  -- ⊢ pair a b₁ < pair a b₂
                           -- ⊢ b₁ * b₁ + a < if a < b₂ then b₂ * b₂ + a else a * a + (a + b₂)
                           -- ⊢ a * a + (a + b₁) < if a < b₂ then b₂ * b₂ + a else a * a + (a + b₂)
  · simp [pair, lt_trans h₁ h, h]
    -- ⊢ b₁ * b₁ < b₂ * b₂
    exact mul_self_lt_mul_self h
    -- 🎉 no goals
  · by_cases h₂ : a < b₂ <;> simp [pair, h₂, h]
    -- ⊢ a * a + (a + b₁) < if a < b₂ then b₂ * b₂ + a else a * a + (a + b₂)
                             -- ⊢ a * a + (a + b₁) < b₂ * b₂ + a
                             -- 🎉 no goals
    simp at h₁
    -- ⊢ a * a + (a + b₁) < b₂ * b₂ + a
    rw [add_comm, add_comm _ a, add_assoc, add_lt_add_iff_left]
    -- ⊢ b₁ + a * a < b₂ * b₂
    rwa [add_comm, ← sqrt_lt, sqrt_add_eq]
    -- ⊢ b₁ ≤ a + a
    exact le_trans h₁ (Nat.le_add_left _ _)
    -- 🎉 no goals
#align nat.mkpair_lt_mkpair_right Nat.pair_lt_pair_right

theorem pair_lt_max_add_one_sq (m n : ℕ) : pair m n < (max m n + 1) ^ 2 := by
  rw [pair, add_sq, mul_one, two_mul, sq, add_assoc, add_assoc]
  -- ⊢ (if m < n then n * n + m else m * m + (m + n)) < max m n * max m n + (max m  …
  cases' (lt_or_le m n) with h h
  -- ⊢ (if m < n then n * n + m else m * m + (m + n)) < max m n * max m n + (max m  …
  rw [if_pos h, max_eq_right h.le, add_lt_add_iff_left, add_assoc]
  -- ⊢ m < n + (n + 1 ^ 2)
  exact h.trans_le (self_le_add_right n _)
  -- ⊢ (if m < n then n * n + m else m * m + (m + n)) < max m n * max m n + (max m  …
  rw [if_neg h.not_lt, max_eq_left h, add_lt_add_iff_left, add_assoc, add_lt_add_iff_left]
  -- ⊢ n < m + 1 ^ 2
  exact lt_succ_of_le h
  -- 🎉 no goals
#align nat.mkpair_lt_max_add_one_sq Nat.pair_lt_max_add_one_sq

theorem max_sq_add_min_le_pair (m n : ℕ) : max m n ^ 2 + min m n ≤ pair m n := by
  rw [pair]
  -- ⊢ max m n ^ 2 + min m n ≤ if m < n then n * n + m else m * m + m + n
  cases' lt_or_le m n with h h
  -- ⊢ max m n ^ 2 + min m n ≤ if m < n then n * n + m else m * m + m + n
  rw [if_pos h, max_eq_right h.le, min_eq_left h.le, sq]
  -- ⊢ max m n ^ 2 + min m n ≤ if m < n then n * n + m else m * m + m + n
  rw [if_neg h.not_lt, max_eq_left h, min_eq_right h, sq, add_assoc, add_le_add_iff_left]
  -- ⊢ n ≤ m + n
  exact le_add_self
  -- 🎉 no goals
#align nat.max_sq_add_min_le_mkpair Nat.max_sq_add_min_le_pair

theorem add_le_pair (m n : ℕ) : m + n ≤ pair m n :=
  (max_sq_add_min_le_pair _ _).trans' <| by
    rw [sq, ← min_add_max, add_comm, add_le_add_iff_right]
    -- ⊢ max m n ≤ max m n * max m n
    exact le_mul_self _
    -- 🎉 no goals
#align nat.add_le_mkpair Nat.add_le_pair

theorem unpair_add_le (n : ℕ) : (unpair n).1 + (unpair n).2 ≤ n :=
  (add_le_pair _ _).trans_eq (pair_unpair _)
#align nat.unpair_add_le Nat.unpair_add_le

end Nat

open Nat

section CompleteLattice

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    ⨆ n : ℕ, f n.unpair.1 n.unpair.2 = ⨆ (i : ℕ) (j : ℕ), f i j := by
  rw [← (iSup_prod : ⨆ i : ℕ × ℕ, f i.1 i.2 = _), ← Nat.surjective_unpair.iSup_comp]
  -- 🎉 no goals
#align supr_unpair iSup_unpair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    ⨅ n : ℕ, f n.unpair.1 n.unpair.2 = ⨅ (i : ℕ) (j : ℕ), f i j :=
  iSup_unpair (show ℕ → ℕ → αᵒᵈ from f)
#align infi_unpair iInf_unpair

end CompleteLattice

namespace Set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem iUnion_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
    ⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Set.iUnion_prod]
  -- ⊢ ⋃ (n : ℕ), s (unpair n).fst ×ˢ t (unpair n).snd = ⋃ (x : ℕ × ℕ), s x.fst ×ˢ  …
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)
  -- 🎉 no goals
#align set.Union_unpair_prod Set.iUnion_unpair_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iUnion_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋃ n : ℕ, f n.unpair.1 n.unpair.2 = ⋃ (i : ℕ) (j : ℕ), f i j :=
  iSup_unpair f
#align set.Union_unpair Set.iUnion_unpair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInter_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋂ n : ℕ, f n.unpair.1 n.unpair.2 = ⋂ (i : ℕ) (j : ℕ), f i j :=
  iInf_unpair f
#align set.Inter_unpair Set.iInter_unpair

end Set
