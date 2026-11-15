/-
Copyright (c) 2026 Omar Muhammad, Arjun Sheth, Vivek Rajesh Joshi, T V H Prathamesh,
Rishi Vyas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Omar Muhammad, Arjun Sheth, Vivek Rajesh Joshi, T V H Prathamesh, Rishi Vyas
-/
module

public import Mathlib.GroupTheory.FreeGroup.Conj

/-!
# Cyclic reduction by structural recursion

Mathlib's `FreeGroup.reduceCyclically` is defined using `List.bidirectionalRec`, which uses
well-founded recursion, so `decide` gets stuck on it. This file gives a definition that
only uses structural recursion: count how many letters at the start of `L` cancel against the
corresponding letters of `L.reverse` (capped at half the length of `L`), and drop that many
letters from each end.

## Main declarations

* `FreeGroup.cancelPrefixLength`: how many leading letters of two words cancel.
* `FreeGroup.reduceCyclicallyDirect`: single-pass cyclic reduction.
* `FreeGroup.reduceCyclicallyDirect_eq`: it agrees with `FreeGroup.reduceCyclically`.
* `FreeGroup.instDecidableRelIsConj`: conjugacy in a free group is decidable, and `decide` can
  evaluate it.
-/

@[expose] public section

open List

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

/-- The number of leading positions at which the letter of `L₂` is the inverse of the letter of
`L₁`, stopping at the first position where it isn't. -/
def cancelPrefixLength : List (α × Bool) → List (α × Bool) → ℕ
  | a :: L₁, b :: L₂ =>
    if b.1 = a.1 ∧ (!b.2) = a.2 then cancelPrefixLength L₁ L₂ + 1 else 0
  | _, _ => 0

theorem min_cancelPrefixLength_append {L₁ L₂ : List (α × Bool)} (s t : List (α × Bool))
    {n : ℕ} (h₁ : n ≤ L₁.length) (h₂ : n ≤ L₂.length) :
    min n (cancelPrefixLength (L₁ ++ s) (L₂ ++ t)) = min n (cancelPrefixLength L₁ L₂) := by
  induction L₁ generalizing L₂ n with
  | nil => simp_all
  | cons a L₁ ih =>
    rcases L₂ with _ | ⟨b, L₂⟩
    · simp_all
    rcases n with _ | n
    · simp
    simp only [cons_append, cancelPrefixLength]
    split
    · simp only [length_cons, Nat.add_le_add_iff_right] at h₁ h₂
      rw [Nat.add_min_add_right, Nat.add_min_add_right, ih h₁ h₂]
    · rfl

/-- Cyclic reduction in a single pass: drop the `k` outermost letters from each end, where `k` is
the number of cancelling outer pairs. Agrees with `reduceCyclically` (see
`reduceCyclicallyDirect_eq`) but is structurally recursive, so `decide` can
evaluate it. -/
def reduceCyclicallyDirect (L : List (α × Bool)) : List (α × Bool) :=
  let k := min (L.length / 2) (cancelPrefixLength L L.reverse)
  (L.drop k).take (L.length - 2 * k)

namespace reduceCyclicallyDirect

@[simp]
protected theorem nil : reduceCyclicallyDirect ([] : List (α × Bool)) = [] := by
  simp [reduceCyclicallyDirect]

@[simp]
protected theorem singleton (a : α × Bool) : reduceCyclicallyDirect [a] = [a] := by
  simp [reduceCyclicallyDirect]

protected theorem cons_append {a b : α × Bool} (L : List (α × Bool)) :
    reduceCyclicallyDirect (a :: (L ++ [b])) =
      if b.1 = a.1 ∧ (!b.2) = a.2 then reduceCyclicallyDirect L else a :: L ++ [b] := by
  have hrev : (a :: (L ++ [b])).reverse = b :: (L.reverse ++ [a]) := by simp
  have hlen : (a :: (L ++ [b])).length = L.length + 2 := by simp
  unfold reduceCyclicallyDirect
  simp only [hrev, hlen, cancelPrefixLength]
  split
  · -- The outer pair cancels
    set k := min (L.length / 2) (cancelPrefixLength L L.reverse) with hk
    have hk' : min ((L.length + 2) / 2)
        (cancelPrefixLength (L ++ [b]) (L.reverse ++ [a]) + 1) = k + 1 := by
      rw [show (L.length + 2) / 2 = L.length / 2 + 1 by omega, Nat.add_min_add_right,
        min_cancelPrefixLength_append _ _ (by omega) (by simp; omega)]
    have hkle : 2 * k ≤ L.length := by grind
    rw [hk', show L.length + 2 - 2 * (k + 1) = L.length - 2 * k by omega,
      drop_succ_cons, drop_append_of_le_length (by omega),
      take_append_of_le_length (by simp; omega)]
  · simp

end reduceCyclicallyDirect

theorem reduceCyclicallyDirect_eq (L : List (α × Bool)) :
    reduceCyclicallyDirect L = reduceCyclically L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton => simp
  | cons_append a L b ih =>
    rw [reduceCyclicallyDirect.cons_append, reduceCyclically.cons_append, ih]

/-- Conjugacy in a free group is decidable, via `FreeGroup.isConj_iff_isRotated`. Built on
`reduceCyclicallyDirect` so that `decide` works. -/
instance instDecidableRelIsConj :
    DecidableRel (IsConj : FreeGroup α → FreeGroup α → Prop) := fun g h ↦
  decidable_of_iff (reduceCyclicallyDirect g.toWord ~r reduceCyclicallyDirect h.toWord) (by
    rw [reduceCyclicallyDirect_eq, reduceCyclicallyDirect_eq]
    exact isConj_iff_isRotated.symm)

end FreeGroup
