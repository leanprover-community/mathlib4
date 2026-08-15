/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.Splitter

/-!
# Binary splitting of dyadic real intervals

This file defines a `Splitter` instance that repeatedly bisects bounded dyadic intervals.
-/

set_option linter.style.header false

@[expose] public section

namespace Inclusion

namespace BinarySplit

/-- Divide a dyadic number by two. -/
def half (x : Dyadic) : Dyadic :=
  match x with
  | .zero => 0
  | .ofOdd n k _ => Dyadic.ofIntWithPrec n (k + 1)

/-- The dyadic midpoint of `a` and `b`. -/
def midpoint (a b : Dyadic) : Dyadic := half (a + b)

/-- Map `F` over the intervals produced by bisecting `I` to depth `n`, coarsening the results. -/
@[specialize]
def coverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β] :
    ℕ → Interval Dyadic → (Interval Dyadic → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match I with
      | ⟨some l, some u⟩ =>
          let m := midpoint l u
          Coarsen.coarsen (Iα := Iβ) (α := β) (coverMap n ⟨l, m⟩ F) (coverMap n ⟨m, u⟩ F)
      | _ => coverMap n I F

theorem mem_coverMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) (I : Interval Dyadic) (F : Interval Dyadic → Iβ) {y : β} {r : ℝ}
    (hr : r ∈ I) (hy : ∀ J, r ∈ J → y ∈ F J) : y ∈ coverMap n I F := by
  induction n generalizing I with
  | zero => exact hy I hr
  | succ n ih =>
      rcases I with ⟨lb, ub⟩
      cases lb with
      | bot => exact ih ⟨⊥, ub⟩ hr
      | coe l =>
        cases ub with
        | top => exact ih ⟨l, ⊤⟩ hr
        | coe u =>
          let m := midpoint l u
          let left : Interval Dyadic := ⟨l, m⟩
          let right : Interval Dyadic := ⟨m, u⟩
          change y ∈ Coarsen.coarsen (Iα := Iβ) (α := β)
            (coverMap n left F) (coverMap n right F)
          by_cases hl : r ≤ Dyadic.toReal m
          · apply Coarsen.mem_coarsen_left (Iα := Iβ) (α := β)
            exact ih left ⟨hr.1, WithTop.coe_le_coe.mpr hl⟩
          · apply Coarsen.mem_coarsen_right (Iα := Iβ) (α := β)
            exact ih right ⟨WithBot.coe_le_coe.mpr (le_of_not_ge hl), hr.2⟩

/-- Cover a dyadic interval by repeatedly bisecting it to depth `n`. -/
def cover (n : ℕ) : Cover (Interval Dyadic) ℝ where
  coverMap := fun I F ↦ coverMap n I F
  mem_coverMap := by
    intro Iβ β _ _ I F x y hx hy
    exact mem_coverMap n I F hx hy

end BinarySplit

instance : Splitter (Interval Dyadic) ℝ where
  cover := BinarySplit.cover

end Inclusion
