/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Init

/-!
# Binary splitting of integer intervals

This file defines the `binarySplit` cover for the `interval_int` inclusion family.
-/

@[expose] public section

namespace Inclusion.IntervalInt

/-- Map `F` over the intervals produced by bisecting `I` to depth `n`, coarsening the results. -/
@[specialize]
def binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β] :
    ℕ → Interval ℤ → (Interval ℤ → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match I with
      | ⟨some l, some u⟩ =>
          if l < u then
            let m := (l + u) / 2
            Coarsen.coarsen β (binarySplitMap n ⟨l, m⟩ F) (binarySplitMap n ⟨m + 1, u⟩ F)
          else F I
      | _ => F I

theorem mem_binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) {I : Interval ℤ} {F : Interval ℤ → Iβ} {y : β} {x : ℤ}
    (hx : x ∈ I) (hy : ∀ J, x ∈ J → y ∈ F J) : y ∈ binarySplitMap n I F := by
  induction n generalizing I with
  | zero => exact hy I hx
  | succ n ih => match I with
    | ⟨some l, some u⟩ =>
      rw [binarySplitMap]
      split
      · let m := (l + u) / 2
        by_cases hl : x ≤ m
        · exact Coarsen.mem_coarsen_left (ih ⟨hx.1, WithTop.coe_le_coe.mpr hl⟩)
        · apply Coarsen.mem_coarsen_right
          exact (ih ⟨WithBot.coe_le_coe.mpr (Int.add_one_le_of_lt (lt_of_not_ge hl)), hx.2⟩)
      · exact hy _ hx
    | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => exact hy _ hx

/-- Cover an integer interval by repeatedly bisecting it to depth `n`. -/
def binarySplit (n : ℕ) : Cover (Interval ℤ) ℤ where
  coverMap := binarySplitMap n
  mem_coverMap := mem_binarySplitMap n

end Inclusion.IntervalInt
