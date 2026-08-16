/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# Binary splitting of dyadic real intervals

This file defines a cover that repeatedly bisects bounded dyadic intervals.
-/

@[expose] public section

namespace Inclusion
namespace IntervalDyadicReal

namespace BinarySplit

/-- The dyadic midpoint of `a` and `b`. -/
def midpoint (a b : Dyadic) : Dyadic :=
  match a + b with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd n (k + 1) hn

/-- Map `F` over the intervals produced by bisecting `I` to depth `n`, coarsening the results. -/
@[specialize]
def coverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β] :
    ℕ → Interval Dyadic → (Interval Dyadic → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          Coarsen.coarsen (α := β) (coverMap n ⟨l, m⟩ F) (coverMap n ⟨m, u⟩ F)
      | _ => F I

theorem mem_coverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) (I : Interval Dyadic) (F : Interval Dyadic → Iβ) {y : β} {r : ℝ}
    (hr : r ∈ I) (hy : ∀ J, r ∈ J → y ∈ F J) : y ∈ coverMap n I F := by
  induction n generalizing I with
  | zero => exact hy I hr
  | succ n ih =>
      rcases I with ⟨lb, ub⟩
      cases lb with
      | bot => exact hy _ hr
      | coe l =>
        cases ub with
        | top => exact hy _ hr
        | coe u =>
          let m := midpoint l u
          let left : Interval Dyadic := ⟨l, m⟩
          let right : Interval Dyadic := ⟨m, u⟩
          by_cases hl : r ≤ Dyadic.toReal m
          · exact Coarsen.mem_coarsen_left
              (ih left ⟨hr.1, WithTop.coe_le_coe.mpr hl⟩)
          · exact Coarsen.mem_coarsen_right
              (ih right ⟨WithBot.coe_le_coe.mpr (le_of_not_ge hl), hr.2⟩)

/-- Cover a dyadic interval by repeatedly bisecting it to depth `n`. -/
def cover (n : ℕ) : Cover (Interval Dyadic) ℝ where
  coverMap := coverMap n
  mem_coverMap hx hy := mem_coverMap n _ _ hx hy

end BinarySplit

end IntervalDyadicReal
end Inclusion
