/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
public import Mathlib.Tactic.Inclusion.Extension.Interval.Basic

/-!
# Binary splitting of intervals

This file defines the shared binary splitting parameter, builder and correctness theorem.
-/

public section

open Lean Qq

namespace Inclusion.Interval

theorem mem_binarySplitMap {α γ Iβ β : Type*} [LinearOrder γ] [ToSet (Interval α) γ]
    [ToSet Iβ β] [Coarsen Iβ β] (f : α → γ) (midpoint : α → α → α) (next : α → α)
    (shouldSplit : α → α → Prop) [DecidableRel shouldSplit]
    (splitMap : ℕ → Interval α → (Interval α → Iβ) → Iβ)
    (hmem : ∀ {x : γ} {I : Interval α}, x ∈ I ↔ x ∈ I.map f)
    (hnext : ∀ {x : γ} {m : α}, f m < x → f (next m) ≤ x)
    (hzero : ∀ I F, splitMap 0 I F = F I)
    (hsucc : ∀ n I F, splitMap (n + 1) I F =
      match I with
      | ⟨some l, some u⟩ =>
          if shouldSplit l u then
            let m := midpoint l u
            Coarsen.coarsen β (splitMap n ⟨l, m⟩ F) (splitMap n ⟨next m, u⟩ F)
          else F I
      | _ => F I)
    (n : ℕ) {I : Interval α} {F : Interval α → Iβ} {x : γ} {y : β}
    (hx : x ∈ I) (hy : ∀ J, x ∈ J → y ∈ F J) : y ∈ splitMap n I F := by
  induction n generalizing I with
  | zero => rw [hzero]; exact hy I hx
  | succ n ih => match I with
    | ⟨some l, some u⟩ =>
      rw [hsucc]
      dsimp only
      split
      · have hx' := hmem.mp hx
        by_cases hl : x ≤ f (midpoint l u)
        · exact Coarsen.mem_coarsen_left (ih (hmem.mpr ⟨hx'.1, WithTop.coe_le_coe.mpr hl⟩))
        · exact Coarsen.mem_coarsen_right
            (ih (hmem.mpr ⟨WithBot.coe_le_coe.mpr (hnext (lt_of_not_ge hl)), hx'.2⟩))
      · exact hy _ hx
    | ⟨⊥, ⊤⟩ | ⟨⊥, some u⟩ | ⟨some l, ⊤⟩ => rw [hsucc]; exact hy _ hx

/-- The maximum depth of binary splitting of bounded intervals. -/
@[inclusion_param]
meta def binarySplitParam : InclusionParamDecl where
  name := `binSplit
  type := q(ℕ)

/-- Construct the binary-splitting cover. -/
meta def mkBinarySplitCover (cover : Expr) : InclusionM (Option Expr) := do
  return (← InclusionM.getParam? `binSplit).map (mkApp cover)

end Inclusion.Interval
