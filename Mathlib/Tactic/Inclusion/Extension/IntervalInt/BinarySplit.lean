/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Init

/-!
# Binary splitting of integer intervals

This file defines the `binarySplit` cover for the `interval_int` inclusion family.
-/

@[expose] public section

namespace Inclusion.IntervalInt

/-- Split a bounded interval in two. -/
def bisect : Interval ℤ → Option (Interval ℤ × Interval ℤ)
  | ⟨some l, some u⟩ =>
      if l < u then
        let m := (l + u) / 2
        some (⟨l, m⟩, ⟨m + 1, u⟩)
      else none
  | _ => none

theorem mem_bisect {I J K : Interval ℤ} {x : ℤ}
    (h : bisect I = some (J, K)) (hx : x ∈ I) : x ∈ J ∨ x ∈ K := by
  match I with
  | ⟨some l, some u⟩ =>
    simp only [bisect, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    by_cases hl : x ≤ (l + u) / 2
    · exact Or.inl ⟨hx.1, WithTop.coe_le_coe.mpr hl⟩
    · exact Or.inr
        ⟨WithBot.coe_le_coe.mpr (Int.add_one_le_of_lt (lt_of_not_ge hl)), hx.2⟩
  | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => simp [bisect] at h

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

theorem binarySplitMap_eq {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) (I : Interval ℤ) (F : Interval ℤ → Iβ) :
    binarySplitMap n I F = Cover.binarySplitMap bisect n I F := by
  induction n generalizing I with
  | zero => rfl
  | succ n ih => match I with
    | ⟨some l, some u⟩ =>
      by_cases h : l < u <;> simp [binarySplitMap, Cover.binarySplitMap, bisect, h, ih]
    | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => rfl

theorem mem_binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) {I : Interval ℤ} {F : Interval ℤ → Iβ} {y : β} {x : ℤ}
    (hx : x ∈ I) (hy : ∀ J, x ∈ J → y ∈ F J) : y ∈ binarySplitMap n I F := by
  rw [binarySplitMap_eq]
  exact Cover.mem_binarySplitMap bisect mem_bisect n hx hy

/-- Cover an integer interval by repeatedly bisecting it to depth `n`. -/
def binarySplit (n : ℕ) : Cover (Interval ℤ) ℤ where
  coverMap := binarySplitMap n
  mem_coverMap := mem_binarySplitMap n

end Inclusion.IntervalInt
