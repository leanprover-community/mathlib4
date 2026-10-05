/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Init
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Binary splitting of dyadic real intervals

This file defines the `binarySplit` cover for the `interval_dyadic_real` inclusion family.
-/

@[expose] public section

open Lean Qq

namespace Inclusion
namespace IntervalDyadicReal

/-- The midpoint of `a` and `b`. -/
def midpoint (a b : Dyadic) : Dyadic :=
  match a + b with
  | .zero => .zero
  | .ofOdd n k hn => .ofOdd n (k + 1) hn

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

theorem mem_binarySplitMap {Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (n : ℕ) {I : Interval Dyadic} {F : Interval Dyadic → Iβ} {y : β} {r : ℝ}
    (hr : r ∈ I) (hy : ∀ J, r ∈ J → y ∈ F J) : y ∈ binarySplitMap n I F := by
  induction n generalizing I with
  | zero => exact hy I hr
  | succ n ih => match I with
    | ⟨some l, some u⟩ =>
      let m := midpoint l u
      by_cases hl : r ≤ Dyadic.toReal m
      · exact Coarsen.mem_coarsen_left (ih ⟨hr.1, WithTop.coe_le_coe.mpr hl⟩)
      · exact Coarsen.mem_coarsen_right (ih ⟨WithBot.coe_le_coe.mpr (le_of_not_ge hl), hr.2⟩)
    | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => exact hy _ hr

/-- Cover a dyadic interval by repeatedly bisecting it to depth `n`. -/
def binarySplit (n : ℕ) : Cover (Interval Dyadic) ℝ where
  coverMap := binarySplitMap n
  mem_coverMap := mem_binarySplitMap n

/-- The depth to which bounded dyadic intervals are repeatedly bisected. A depth of
`n` produces `2 ^ n` pieces. -/
@[inclusion_param]
meta def binarySplitParam : InclusionParamDecl where
  name := `binSplit
  type := q(ℕ)

/-- Construct the binary-splitting cover with `2 ^ n` pieces. -/
meta def mkBinarySplitCover : InclusionM (Option Expr) := do
  let some depth ← InclusionM.getParam? `binSplit | return none
  return some (mkApp (mkConst ``binarySplit [.zero]) depth)

end IntervalDyadicReal
end Inclusion
