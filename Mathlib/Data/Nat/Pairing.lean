/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.pairing
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.MinMax

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
def mkPair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b
#align nat.mkpair Nat.mkPair

/-- Unpairing function for the natural numbers. -/
-- porting notes: no pp_nodot
--@[pp_nodot]
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)
#align nat.unpair Nat.unpair

@[simp]
theorem mkPair_unpair (n : ℕ) : mkPair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := add_tsub_cancel_of_le (sqrt_le _)
  split_ifs with h
  · simp [mkPair, h, sm]
  · have hl : n - s * s - s ≤ s :=
      tsub_le_iff_left.mpr (tsub_le_iff_left.mpr <| by rw [← add_assoc] ; apply sqrt_le_add)
    simp [mkPair, hl.not_lt, add_assoc, add_tsub_cancel_of_le (le_of_not_gt h), sm]
#align nat.mkpair_unpair Nat.mkPair_unpair

theorem mkPair_unpair' {n a b} (H : unpair n = (a, b)) : mkPair a b = n := by
  simpa [H] using mkPair_unpair n
#align nat.mkpair_unpair' Nat.mkPair_unpair'

@[simp]
theorem unpair_mkPair (a b : ℕ) : unpair (mkPair a b) = (a, b) := by
  dsimp only [mkPair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, add_tsub_cancel_right, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact add_le_add_left (le_of_not_gt h) _
    simp [unpair, ae, Nat.not_lt_zero, add_assoc]
#align nat.unpair_mkpair Nat.unpair_mkPair

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps (config := { fullyApplied := false })]
def mkPairEquiv : ℕ × ℕ ≃ ℕ :=
  ⟨uncurry mkPair, unpair, fun ⟨a, b⟩ => unpair_mkPair a b, mkPair_unpair⟩
#align nat.mkpair_equiv Nat.mkPairEquiv
#align nat.mkpair_equiv_apply Nat.mkPairEquiv_apply
#align nat.mkpair_equiv_symm_apply Nat.mkPairEquiv_symm_apply

theorem surjective_unpair : Surjective unpair :=
  mkPairEquiv.symm.surjective
#align nat.surjective_unpair Nat.surjective_unpair

@[simp]
theorem mkPair_eq_mkPair {a b c d : ℕ} : mkPair a b = mkPair c d ↔ a = c ∧ b = d :=
  mkPairEquiv.injective.eq_iff.trans (@Prod.ext_iff ℕ ℕ (a, b) (c, d))
#align nat.mkpair_eq_mkpair Nat.mkPair_eq_mkPair

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n := by
  let s := sqrt n
  simp [unpair];
  by_cases h : n - s * s < s <;> simp [h]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (tsub_lt_self n1 (mul_pos s0 s0))
#align nat.unpair_lt Nat.unpair_lt

@[simp]
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  simp
#align nat.unpair_zero Nat.unpair_zero

theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
  | 0 => by simp
  | n + 1 => le_of_lt (unpair_lt (Nat.succ_pos _))
#align nat.unpair_left_le Nat.unpair_left_le

theorem left_le_mkPair (a b : ℕ) : a ≤ mkPair a b := by simpa using unpair_left_le (mkPair a b)
#align nat.left_le_mkpair Nat.left_le_mkPair

theorem right_le_mkPair (a b : ℕ) : b ≤ mkPair a b := by
  by_cases h : a < b <;> simp [mkPair, h]
  exact le_trans (le_mul_self _) (Nat.le_add_right _ _)
#align nat.right_le_mkpair Nat.right_le_mkPair

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n := by
  simpa using right_le_mkPair n.unpair.1 n.unpair.2
#align nat.unpair_right_le Nat.unpair_right_le

theorem mkPair_lt_mkPair_left {a₁ a₂} (b) (h : a₁ < a₂) : mkPair a₁ b < mkPair a₂ b := by
  by_cases h₁ : a₁ < b <;> simp [mkPair, h₁, add_assoc]
  · by_cases h₂ : a₂ < b <;> simp [mkPair, h₂, h]
    simp at h₂
    apply add_lt_add_of_le_of_lt
    exact mul_self_le_mul_self h₂
    exact Nat.lt_add_right _ _ _ h
  · simp at h₁
    simp [not_lt_of_gt (lt_of_le_of_lt h₁ h)]
    apply add_lt_add
    exact mul_self_lt_mul_self h
    apply add_lt_add_right ; assumption
#align nat.mkpair_lt_mkpair_left Nat.mkPair_lt_mkPair_left

theorem mkPair_lt_mkPair_right (a) {b₁ b₂} (h : b₁ < b₂) : mkPair a b₁ < mkPair a b₂ := by
  by_cases h₁ : a < b₁ <;> simp [mkPair, h₁, add_assoc]
  · simp [mkPair, lt_trans h₁ h, h]
    exact mul_self_lt_mul_self h
  · by_cases h₂ : a < b₂ <;> simp [mkPair, h₂, h]
    simp at h₁
    rw [add_comm, add_comm _ a, add_assoc, add_lt_add_iff_left]
    rwa [add_comm, ← sqrt_lt, sqrt_add_eq]
    exact le_trans h₁ (Nat.le_add_left _ _)
#align nat.mkpair_lt_mkpair_right Nat.mkPair_lt_mkPair_right

theorem mkPair_lt_max_add_one_sq (m n : ℕ) : mkPair m n < (max m n + 1) ^ 2 := by
  rw [mkPair, add_sq, mul_one, two_mul, sq, add_assoc, add_assoc]
  cases' (lt_or_le m n) with h h
  rw [if_pos h, max_eq_right h.le, add_lt_add_iff_left, add_assoc]
  exact h.trans_le (self_le_add_right n _)
  rw [if_neg h.not_lt, max_eq_left h, add_lt_add_iff_left, add_assoc, add_lt_add_iff_left]
  exact lt_succ_of_le h
#align nat.mkpair_lt_max_add_one_sq Nat.mkPair_lt_max_add_one_sq

theorem max_sq_add_min_le_mkPair (m n : ℕ) : max m n ^ 2 + min m n ≤ mkPair m n := by
  rw [mkPair]
  cases' lt_or_le m n with h h
  rw [if_pos h, max_eq_right h.le, min_eq_left h.le, sq]
  rw [if_neg h.not_lt, max_eq_left h, min_eq_right h, sq, add_assoc, add_le_add_iff_left]
  exact le_add_self
#align nat.max_sq_add_min_le_mkpair Nat.max_sq_add_min_le_mkPair

theorem add_le_mkPair (m n : ℕ) : m + n ≤ mkPair m n :=
  (max_sq_add_min_le_mkPair _ _).trans' <| by
    rw [sq, ← min_add_max, add_comm, add_le_add_iff_right]
    exact le_mul_self _
#align nat.add_le_mkpair Nat.add_le_mkPair

theorem unpair_add_le (n : ℕ) : (unpair n).1 + (unpair n).2 ≤ n :=
  (add_le_mkPair _ _).trans_eq (mkPair_unpair _)
#align nat.unpair_add_le Nat.unpair_add_le

end Nat

open Nat

section CompleteLattice

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    (⨆ n : ℕ, f n.unpair.1 n.unpair.2) = ⨆ (i : ℕ) (j : ℕ), f i j := by
  rw [← (supᵢ_prod : (⨆ i : ℕ × ℕ, f i.1 i.2) = _), ← Nat.surjective_unpair.supᵢ_comp]
#align supr_unpair supᵢ_unpair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    (⨅ n : ℕ, f n.unpair.1 n.unpair.2) = ⨅ (i : ℕ) (j : ℕ), f i j :=
  supᵢ_unpair (show ℕ → ℕ → αᵒᵈ from f)
#align infi_unpair infᵢ_unpair

end CompleteLattice

namespace Set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem unionᵢ_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
    (⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd) = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Set.unionᵢ_prod]
  exact surjective_unpair.unionᵢ_comp (fun x => s x.fst ×ˢ t x.snd)
#align set.Union_unpair_prod Set.unionᵢ_unpair_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ_unpair {α} (f : ℕ → ℕ → Set α) :
    (⋃ n : ℕ, f n.unpair.1 n.unpair.2) = ⋃ (i : ℕ) (j : ℕ), f i j :=
  supᵢ_unpair f
#align set.Union_unpair Set.unionᵢ_unpair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ_unpair {α} (f : ℕ → ℕ → Set α) :
    (⋂ n : ℕ, f n.unpair.1 n.unpair.2) = ⋂ (i : ℕ) (j : ℕ), f i j :=
  infᵢ_unpair f
#align set.Inter_unpair Set.interᵢ_unpair

end Set
