/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Init

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Binary splitting of dyadic real intervals

This file defines the `binarySplit` cover for the `interval_dyadic_real` inclusion family.
-/

@[expose] public section

namespace Inclusion
namespace IntervalDyadicReal

/-- The midpoint of `a` and `b`. -/
def midpoint (a b : Dyadic) : Dyadic :=
  match a + b with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd n (k + 1) hn

/-- Split a bounded interval in two. -/
def bisect : Interval Dyadic → Option (Interval Dyadic × Interval Dyadic)
  | ⟨some l, some u⟩ =>
      let m := midpoint l u
      some (⟨l, m⟩, ⟨m, u⟩)
  | _ => none

theorem mem_bisect {I J K : Interval Dyadic} {r : ℝ}
    (h : bisect I = some (J, K)) (hr : r ∈ I) : r ∈ J ∨ r ∈ K := by
  match I with
  | ⟨some l, some u⟩ =>
    cases h
    by_cases hl : r ≤ (midpoint l u).toReal
    · exact Or.inl ⟨hr.1, WithTop.coe_le_coe.mpr hl⟩
    · exact Or.inr ⟨WithBot.coe_le_coe.mpr (le_of_not_ge hl), hr.2⟩
  | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => simp [bisect] at h

/-- Map `F` over the intervals produced by bisecting `I` to depth `n`, coarsening the results. -/
@[specialize]
def binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β] :
    ℕ → Interval Dyadic → (Interval Dyadic → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          Coarsen.coarsen β (binarySplitMap n ⟨l, m⟩ F) (binarySplitMap n ⟨m, u⟩ F)
      | _ => F I

theorem binarySplitMap_eq {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) (I : Interval Dyadic) (F : Interval Dyadic → Iβ) :
    binarySplitMap n I F = Cover.binarySplitMap bisect n I F := by
  induction n generalizing I with
  | zero => rfl
  | succ n ih => match I with
    | ⟨some l, some u⟩ =>
      simp [binarySplitMap, Cover.binarySplitMap, bisect, ih]
    | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => rfl

theorem mem_binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) {I : Interval Dyadic} {F : Interval Dyadic → Iβ} {y : β} {r : ℝ}
    (hr : r ∈ I) (hy : ∀ J, r ∈ J → y ∈ F J) : y ∈ binarySplitMap n I F := by
  rw [binarySplitMap_eq]
  exact Cover.mem_binarySplitMap bisect mem_bisect n hr hy

/-- Cover a dyadic interval by repeatedly bisecting it to depth `n`. -/
def binarySplit (n : ℕ) : Cover (Interval Dyadic) ℝ where
  coverMap := binarySplitMap n
  mem_coverMap := mem_binarySplitMap n

end IntervalDyadicReal
end Inclusion
